import json
import logging
import sys
from pathlib import Path

import pytest
from flask import Flask

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from src.blockchain.block import Block  # noqa: E402
from src.blockchain.chain import Blockchain  # noqa: E402
from src.network.voting import setup_voting_routes  # noqa: E402


def load_genai_cases(filename: str):
    path = PROJECT_ROOT / "tests" / "inputs" / filename
    return json.loads(path.read_text())


GENAI_VOTES_CASES = {case["id"]: case for case in load_genai_cases("genai_votes_cases.json")}


def _append_block(blockchain: Blockchain, transactions):
    """Helper to append a mined block with specified transactions."""
    latest = blockchain.get_latest_block()
    block = Block(
        index=latest.index + 1,
        transactions=transactions,
        previous_hash=latest.hash,
        difficulty=1
    )
    block.mine_block()
    blockchain.chain.append(block)
    return block


@pytest.fixture()
def votes_client():
    """Provide Flask client wired to /votes with isolated blockchain state."""
    app = Flask(__name__)
    app.testing = True
    blockchain = Blockchain()
    logger = logging.getLogger("test-votes")
    logger.addHandler(logging.NullHandler())

    setup_voting_routes(app, blockchain, logger)

    with app.test_client() as client:
        yield client, blockchain


def test_votes_counts_multiple_candidates(votes_client):
    client, blockchain = votes_client
    _append_block(blockchain, [
        {'sender': 'v1', 'recipient': 'alice', 'amount': 1},
        {'sender': 'v2', 'recipient': 'bob', 'amount': 1},
        {'sender': 'v3', 'recipient': 'alice', 'amount': 1}
    ])

    resp = client.get('/votes')
    assert resp.status_code == 200
    data = resp.get_json()['data']

    counts = {entry['candidate']: entry['votes'] for entry in data['results']}
    assert counts == {'alice': 2, 'bob': 1}
    assert data['total_votes'] == 3
    latest_ts = blockchain.chain[-1].timestamp
    assert data['last_updated'] >= latest_ts


def test_votes_ignores_non_vote_transactions(votes_client):
    client, blockchain = votes_client
    case = GENAI_VOTES_CASES["VOTES_MIXED_AMOUNTS"]
    _append_block(blockchain, case["transactions"])

    resp = client.get('/votes')
    assert resp.status_code == 200
    data = resp.get_json()['data']

    counts = {entry['candidate']: entry['votes'] for entry in data['results']}
    assert counts == case["expected_totals"]
    assert data['total_votes'] == sum(case["expected_totals"].values())


def test_votes_empty_chain_returns_zero(votes_client):
    client, _ = votes_client
    resp = client.get('/votes')
    assert resp.status_code == 200
    data = resp.get_json()['data']
    assert data['results'] == []
    assert data['total_votes'] == 0


def test_votes_case_sensitive_candidates(votes_client):
    client, blockchain = votes_client
    _append_block(blockchain, [
        {'sender': 'v1', 'recipient': 'Zoe', 'amount': 1},
        {'sender': 'v2', 'recipient': 'zoe', 'amount': 1}
    ])

    resp = client.get('/votes')
    assert resp.status_code == 200
    data = resp.get_json()['data']
    counts = {entry['candidate']: entry['votes'] for entry in data['results']}
    assert counts == {'Zoe': 1, 'zoe': 1}


def test_votes_handles_malicious_transaction_missing_recipient(votes_client):
    client, blockchain = votes_client
    case = GENAI_VOTES_CASES["VOTES_MISSING_RECIPIENT"]
    _append_block(blockchain, case["transactions"])

    resp = client.get('/votes')

    assert resp.status_code == 200
    data = resp.get_json()['data']
    assert data['results'] == []
    assert data['total_votes'] == case.get("expected_total_votes", 0)

