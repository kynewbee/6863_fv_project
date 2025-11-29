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
from src.network.voting import setup_voting_routes, voted_users  # noqa: E402


def load_genai_cases(filename: str):
    path = PROJECT_ROOT / "tests" / "inputs" / filename
    return json.loads(path.read_text())


GENAI_STATUS_CASES = {case["id"]: case for case in load_genai_cases("genai_vote_status_cases.json")}


def _append_block(blockchain: Blockchain, transactions):
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
def status_client():
    app = Flask(__name__)
    app.testing = True
    blockchain = Blockchain()
    logger = logging.getLogger("test-vote-status")
    logger.addHandler(logging.NullHandler())

    voted_users.clear()
    setup_voting_routes(app, blockchain, logger)

    with app.test_client() as client:
        yield client, blockchain

    voted_users.clear()


def test_vote_status_requires_voter_param(status_client):
    client, _ = status_client
    resp = client.get('/vote_status')
    assert resp.status_code == 400
    assert resp.get_json()['message'] == 'Missing voter ID'


def test_vote_status_reports_not_voted(status_client):
    client, _ = status_client
    case = GENAI_STATUS_CASES["STATUS_NOT_VOTED_LONG_ID"]
    resp = client.get(f'/vote_status?voter={case["voter"]}')
    data = resp.get_json()['data']

    assert resp.status_code == 200
    assert data['has_voted'] is case["expected_has_voted"]
    assert data['voted_candidate'] is None
    assert data['vote_time'] is None
    assert data['block_height'] is None


def test_vote_status_returns_latest_vote_details(status_client):
    client, blockchain = status_client

    first_block = _append_block(blockchain, [
        {'sender': 'alice', 'recipient': 'bob', 'amount': 1}
    ])
    second_block = _append_block(blockchain, [
        {'sender': 'alice', 'recipient': 'carol', 'amount': 1}
    ])
    voted_users.add('alice')

    resp = client.get('/vote_status?voter=alice')
    data = resp.get_json()['data']

    assert resp.status_code == 200
    assert data['has_voted'] is True
    assert data['voted_candidate'] == 'carol'
    assert data['block_height'] == second_block.index
    assert data['vote_time'] == second_block.timestamp


def test_vote_status_with_sql_like_voter(status_client):
    client, _ = status_client
    case = GENAI_STATUS_CASES["STATUS_SQLI_STYLE"]
    resp = client.get(f'/vote_status?voter={case["voter"]}')
    data = resp.get_json()['data']

    assert resp.status_code == 200
    assert data['has_voted'] is case["expected_has_voted"]


def test_vote_status_inconsistent_state_sets_has_voted_false(status_client):
    client, _ = status_client
    case = GENAI_STATUS_CASES["STATUS_INCONSISTENT_STATE"]
    voted_users.add(case["voter"])

    resp = client.get(f'/vote_status?voter={case["voter"]}')
    data = resp.get_json()['data']

    # 规范要求：若链中找不到对应交易，应返回 has_voted=False
    assert resp.status_code == 200
    assert data['has_voted'] is case["expected_has_voted"]
    assert data['voted_candidate'] is None
    assert data['vote_time'] is None
    assert data['block_height'] is None

