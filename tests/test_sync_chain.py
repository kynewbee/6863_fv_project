import json
import logging
import sys
from pathlib import Path

import pytest
import requests

PROJECT_ROOT = Path(__file__).resolve().parents[1]
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from src.blockchain.chain import Blockchain  # noqa: E402
from src.network import client as client_module  # noqa: E402


def load_genai_cases(filename: str):
    path = PROJECT_ROOT / "tests" / "inputs" / filename
    return json.loads(path.read_text())


SYNC_CASES = {case["id"]: case for case in load_genai_cases("genai_sync_cases.json")}


def build_chain(num_blocks: int) -> Blockchain:
    chain = Blockchain()
    for i in range(num_blocks - 1):
        chain.add_transaction({'sender': f'sender{i}', 'recipient': 'rcp', 'amount': 1})
        chain.mine_pending_transactions()
    return chain


@pytest.fixture()
def sync_context(monkeypatch):
    chain = build_chain(2)
    logger = logging.getLogger("test-sync")
    logger.addHandler(logging.NullHandler())

    monkeypatch.setattr(client_module, "blockchain", chain)
    monkeypatch.setattr(client_module, "peers", {'http://peer1'})
    monkeypatch.setattr(client_module, "client_logger", logger)
    monkeypatch.setattr(client_module, "get_base_url", lambda: "http://local")
    return chain


class FakeResponse:
    def __init__(self, data):
        self._data = data

    def json(self):
        return self._data


def test_sync_chain_replaces_with_longer_chain(monkeypatch, sync_context):
    _ = SYNC_CASES["SYNC_LONGER_CHAIN"]
    local_chain = sync_context
    remote_chain = build_chain(3)
    monkeypatch.setattr(requests, "get", lambda url, timeout: FakeResponse(remote_chain.to_dict()))

    result = client_module.sync_chain()
    assert result is True
    assert len(client_module.blockchain.chain) == len(remote_chain.chain)


def test_sync_chain_replaces_equal_length_higher_work(monkeypatch, sync_context):
    _ = SYNC_CASES["SYNC_EQUAL_LENGTH_HIGHER_WORK"]
    local_chain = sync_context
    remote_chain = build_chain(len(local_chain.chain))

    def fake_from_dict(cls, _):
        return remote_chain

    monkeypatch.setattr(requests, "get", lambda url, timeout: FakeResponse({}))
    monkeypatch.setattr(Blockchain, "from_dict", classmethod(fake_from_dict))

    def fake_work(self):
        if self is remote_chain:
            return 200
        return 100

    monkeypatch.setattr(Blockchain, "calculate_work", fake_work, raising=False)

    result = client_module.sync_chain()
    assert result is True
    assert len(client_module.blockchain.chain) == len(remote_chain.chain)
    assert client_module.blockchain.chain[-1].hash == remote_chain.chain[-1].hash


def test_sync_chain_rejects_invalid_chain(monkeypatch, sync_context):
    _ = SYNC_CASES["SYNC_INVALID_CHAIN"]
    invalid_chain = build_chain(3)
    invalid_data = invalid_chain.to_dict()
    invalid_data['chain'][1]['previous_hash'] = 'deadbeef'

    monkeypatch.setattr(requests, "get", lambda url, timeout: FakeResponse(invalid_data))
    before_len = len(sync_context.chain)
    result = client_module.sync_chain()
    assert result is False
    assert len(client_module.blockchain.chain) == before_len


def test_sync_chain_handles_shorter_chain(monkeypatch, sync_context):
    _ = SYNC_CASES["SYNC_SHORTER_CHAIN"]
    shorter_chain = build_chain(1)
    monkeypatch.setattr(requests, "get", lambda url, timeout: FakeResponse(shorter_chain.to_dict()))

    before_len = len(sync_context.chain)
    result = client_module.sync_chain()
    assert result is False
    assert len(client_module.blockchain.chain) == before_len


def test_sync_chain_handles_network_error(monkeypatch, sync_context):
    _ = SYNC_CASES["SYNC_NETWORK_ERROR"]
    def raise_error(*args, **kwargs):
        raise requests.exceptions.ConnectionError("boom")

    monkeypatch.setattr(requests, "get", raise_error)

    before_len = len(sync_context.chain)
    result = client_module.sync_chain()
    assert result is False
    assert len(client_module.blockchain.chain) == before_len

