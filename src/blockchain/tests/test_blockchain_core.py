import time
from ..block import Block, compute_merkle_root
from ..chain import Blockchain

# Merkle Root
def test_compute_merkle_root_empty_list():
    """
    空交易列表时，Merkle root 应该是 64 位的全 0（你现在代码里就是这么写的）。
    """
    root = compute_merkle_root([])
    assert isinstance(root, str)
    assert len(root) == 64
    assert set(root) == {"0"}


def test_compute_merkle_root_single_value():
    """
    单个 hash 时，Merkle root 应该等于那个 hash 本身。
    """
    tx_hash = "a" * 64
    root = compute_merkle_root([tx_hash])
    assert root == tx_hash

# Block.mine_block
def test_mine_block_respects_difficulty():
    """
    测试 Block.mine_block()：
    - 最终 hash 一定满足前缀 0*difficulty
    """
    difficulty = 3
    txs = [{"from": "Alice", "to": "Bob", "amount": 1}]
    previous_hash = "0" * 64

    # 假设 Block 构造函数签名类似：
    # Block(index, transactions, previous_hash, timestamp=None, difficulty=2)
    block = Block(
        index=1,
        transactions=txs,
        previous_hash=previous_hash,
        timestamp=time.time(),
        difficulty=difficulty,
    )

    # 如果你的 __init__ 里还没算 hash，这里先初始化一次
    if not hasattr(block, "hash") or not isinstance(block.hash, str):
        block.hash = block.calculate_hash()

    block.mine_block()

    assert isinstance(block.hash, str)
    assert block.hash.startswith("0" * difficulty)
    # 通常 mine 结束后，当前状态下重新计算 hash 应该一致
    assert block.hash == block.calculate_hash()

# add_transaction + mine_pending_transactions
def test_add_transaction_and_mine_pending_transactions():
    """
    测试区块链挖矿流程：
    - add_transaction 后 pending_transactions 中有该交易
    - mine_pending_transactions 之后：
        * 链长度 +1
        * 新区块在链中
        * 新区块包含刚刚的交易
        * pending_transactions 被清空
    """
    bc = Blockchain()

    tx = {"sender": "Alice", "recipient": "Bob", "amount": 1}
    bc.add_transaction(tx)

    # 1. 交易应当进入 pending_transactions
    assert tx in bc.pending_transactions

    old_len = len(bc.chain)

    new_block = bc.mine_pending_transactions()

    # 2. 链长度增加 1
    assert len(bc.chain) == old_len + 1

    # 3. 新区块在链中
    assert new_block is bc.chain[-1]

    # 4. 新区块包含之前 pending 的交易
    assert tx in new_block.transactions

    # 5. pending_transactions 被清空
    assert bc.pending_transactions == []

# is_chain_valid
def test_is_chain_valid_after_mining():
    """
    正常添加交易并挖矿后，区块链应该保持有效。
    """
    bc = Blockchain()

    # 添加几笔交易
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
    如果中间某个区块被篡改（不重新计算 hash），
    is_chain_valid() 应该检测到并返回 False。
    """
    bc = Blockchain()
    bc.add_transaction({"sender": "Alice", "recipient": "Bob", "amount": 1})
    bc.mine_pending_transactions()

    # 篡改最新区块的交易，但不更新 hash
    last_block = bc.chain[-1]
    if last_block.transactions:
        last_block.transactions[0]["amount"] = 999  # 修改金额

    assert bc.is_chain_valid() is False




