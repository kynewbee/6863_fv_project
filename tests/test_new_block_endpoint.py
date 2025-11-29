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


def load_genai_cases(filename: str):
    path = Path(__file__).resolve().parents[1] / "tests" / "inputs" / filename
    return json.loads(path.read_text())


BLOCK_CASES = {case["id"]: case for case in load_genai_cases("genai_block_cases.json")}


@pytest.fixture()
def client_app(monkeypatch):
    from src.blockchain.chain import Blockchain
    from src.network import client as client_module

    new_chain = Blockchain()
    monkeypatch.setattr(client_module, "blockchain", new_chain)
    monkeypatch.setattr(client_module, "peers", set())

    test_app = Flask(__name__)
    client_logger = logging.getLogger("test-client")
    client_logger.addHandler(logging.NullHandler())
    monkeypatch.setattr(client_module, "app", test_app)
    monkeypatch.setattr(client_module, "client_logger", client_logger)

    # Re-bind the /new_block route to the fresh app
    @test_app.route('/new_block', methods=['POST'])
    def new_block_endpoint():
        return client_module.receive_block()

    with test_app.test_client() as flask_client:
        yield flask_client, new_chain


def _make_block(previous_block: Block, difficulty: int = 1):
    block = Block(
        index=previous_block.index + 1,
        transactions=[{'sender': 'v', 'recipient': 'c', 'amount': 1}],
        previous_hash=previous_block.hash,
        difficulty=difficulty
    )
    block.mine_block()
    return block


def test_new_block_accepts_valid_block(client_app):
    client, chain = client_app
    case = BLOCK_CASES["BLOCK_VALID_STANDARD"]
    block = _make_block(chain.get_latest_block(), difficulty=chain.difficulty)

    resp = client.post('/new_block', json=block.to_dict())
    assert resp.status_code == case["expected_status"]
    assert resp.get_json()['status'] == 'accepted'
    assert chain.chain[-1].hash == block.hash


def test_new_block_rejects_invalid_hash(client_app):
    client, chain = client_app
    case = BLOCK_CASES["BLOCK_HASH_MISMATCH"]
    block = _make_block(chain.get_latest_block())
    payload = block.to_dict()
    payload.update(case["mutation"])

    resp = client.post('/new_block', json=payload)
    assert resp.status_code == case["expected_status"]
    assert resp.get_json()['reason'] == case["expected_reason"]


def test_new_block_rejects_wrong_previous_hash(client_app):
    client, chain = client_app
    case = BLOCK_CASES["BLOCK_PREV_HASH_MISMATCH"]
    block = _make_block(chain.get_latest_block())
    payload = block.to_dict()
    payload.update(case["mutation"])

    resp = client.post('/new_block', json=payload)
    assert resp.status_code == case["expected_status"]
    assert resp.get_json()['reason'] == case["expected_reason"]


def test_new_block_rejects_invalid_pow(client_app):
    client, chain = client_app
    case = BLOCK_CASES["BLOCK_INVALID_POW"]
    block = _make_block(chain.get_latest_block(), difficulty=chain.difficulty)
    payload = block.to_dict()
    payload.update(case["mutation"])

    resp = client.post('/new_block', json=payload)
    assert resp.status_code == case["expected_status"]
    assert resp.get_json()['reason'] == case["expected_reason"]


def test_new_block_rejects_missing_fields(client_app):
    client, _ = client_app
    case = BLOCK_CASES["BLOCK_MISSING_FIELDS"]
    resp = client.post('/new_block', json=case["custom_payload"])
    assert resp.status_code == case["expected_status"]
    assert resp.get_json()['reason'].startswith(case["expected_reason"])

