import time
from ..block import Block, compute_merkle_root
from ..chain import Blockchain

# Merkle Root
def test_compute_merkle_root_empty_list():
    """
    When the transaction list is empty, the Merkle root should be
    a 64-character string of all zeros (as implemented in your code).
    """
    root = compute_merkle_root([])
    assert isinstance(root, str)
    assert len(root) == 64
    assert set(root) == {"0"}


def test_compute_merkle_root_single_value():
    """
    When there is only one hash, the Merkle root should equal that hash.
    """
    tx_hash = "a" * 64
    root = compute_merkle_root([tx_hash])
    assert root == tx_hash

# Block.mine_block
def test_mine_block_respects_difficulty():
    """
    Test Block.mine_block():
    - The final hash must satisfy the prefix of 0 * difficulty.
    """
    difficulty = 3
    txs = [{"from": "Alice", "to": "Bob", "amount": 1}]
    previous_hash = "0" * 64

    # Assume Block constructor signature looks like:
    # Block(index, transactions, previous_hash, timestamp=None, difficulty=2)
    block = Block(
        index=1,
        transactions=txs,
        previous_hash=previous_hash,
        timestamp=time.time(),
        difficulty=difficulty,
    )

    # If your __init__ does not compute hash yet, initialize it once here
    if not hasattr(block, "hash") or not isinstance(block.hash, str):
        block.hash = block.calculate_hash()

    block.mine_block()

    assert isinstance(block.hash, str)
    assert block.hash.startswith("0" * difficulty)
    # After mining, recalculating the hash should produce the same result
    assert block.hash == block.calculate_hash()

# add_transaction + mine_pending_transactions
def test_add_transaction_and_mine_pending_transactions():
    """
    Test the mining workflow of the blockchain:
    - After add_transaction, the transaction should be in pending_transactions.
    - After mine_pending_transactions:
        * The chain length should increase by 1.
        * The new block should be appended to the chain.
        * The new block should contain the previous pending transaction(s).
        * pending_transactions should be cleared.
    """
    bc = Blockchain()

    tx = {"sender": "Alice", "recipient": "Bob", "amount": 1}
    bc.add_transaction(tx)

    # 1. The transaction should be added to pending_transactions
    assert tx in bc.pending_transactions

    old_len = len(bc.chain)

    new_block = bc.mine_pending_transactions()

    # 2. The chain length should increase by 1
    assert len(bc.chain) == old_len + 1

    # 3. The new block should be in the chain
    assert new_block is bc.chain[-1]

    # 4. The new block should contain the pending transaction
    assert tx in new_block.transactions

    # 5. pending_transactions should be cleared
    assert bc.pending_transactions == []

# is_chain_valid
def test_is_chain_valid_after_mining():
    """
    After adding transactions and mining, the blockchain should remain valid.
    """
    bc = Blockchain()

    # Add several transactions
    for i in range(3):
        bc.add_transaction({
            "sender": f"user{i}",
            "recipient": f"user{i+1}",
            "amount": 1,
        })

    bc.mine_pending_transactions()

    assert bc.is_chain_valid() is True

def test_is_chain_invalid_if_block_tampered():
    """
    If a block in the chain is tampered with (without recomputing the hash),
    is_chain_valid() should detect it and return False.
    """
    bc = Blockchain()
    bc.add_transaction({"sender": "Alice", "recipient": "Bob", "amount": 1})
    bc.mine_pending_transactions()

    # Tamper with the most recent block's transaction without updating the hash
    last_block = bc.chain[-1]
    if last_block.transactions:
        last_block.transactions[0]["amount"] = 999  # Modify amount

    assert bc.is_chain_valid() is False