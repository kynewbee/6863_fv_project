import json
import logging
import sys
from pathlib import Path

import pytest
from flask import Flask

# Ensure project root is importable
PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from src.blockchain.chain import Blockchain  # noqa: E402
from src.network.voting import setup_voting_routes, voted_users  # noqa: E402


def load_genai_cases(filename: str):
    path = PROJECT_ROOT / "tests" / "inputs" / filename
    return json.loads(path.read_text())


GENAI_VOTE_CASES = {case["id"]: case for case in load_genai_cases("genai_vote_cases.json")}


@pytest.fixture()
def voting_client():
    """Create an isolated Flask test client wired to the voting routes."""
    app = Flask(__name__)
    app.testing = True
    blockchain = Blockchain()
    logger = logging.getLogger("test-voting")
    logger.addHandler(logging.NullHandler())

    voted_users.clear()
    setup_voting_routes(app, blockchain, logger)

    with app.test_client() as client:
        yield client, blockchain

    voted_users.clear()


def test_vote_success_persists_transaction(voting_client):
    client, blockchain = voting_client
    case = GENAI_VOTE_CASES["VOTE_VALID_STANDARD"]

    resp = client.post('/vote', json=case["payload"])
    body = resp.get_json()

    assert resp.status_code == 200
    assert body['status'] == 'success'
    assert blockchain.pending_transactions[-1] == {
        'sender': case["payload"]["voter"],
        'recipient': case["payload"]["candidate"],
        'amount': 1
    }
    assert case["payload"]["voter"] in voted_users


def test_vote_duplicate_voter_rejected(voting_client):
    client, _ = voting_client

    resp1 = client.post('/vote', json={'voter': 'carol', 'candidate': 'bob'})
    assert resp1.status_code == 200

    resp2 = client.post('/vote', json={'voter': 'carol', 'candidate': 'dave'})
    body = resp2.get_json()

    assert resp2.status_code == 400
    assert body['status'] == 'error'
    assert 'already voted' in body['message']


AI_CASES = [
    case for case_id, case in GENAI_VOTE_CASES.items()
    if case_id != "VOTE_VALID_STANDARD"
]


@pytest.mark.parametrize("case", AI_CASES, ids=lambda c: c["id"])
def test_vote_genai_cases(voting_client, case):
    client, _ = voting_client

    transport = case.get("transport", "json")
    if transport == "form":
        resp = client.post('/vote', data=case["raw"])
    else:
        resp = client.post('/vote', json=case["payload"])

    assert resp.status_code == case["expected_status"]

