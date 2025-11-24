from typing import List, Dict, Any
from .block import Block
import time

from icontract import require, ensure

class Blockchain:
    """
    Blockchain class managing the chain of blocks.
    Handles block creation, validation, and difficulty adjustment.
    """

    chain: List[Block]
    pending_transactions: List[Dict[str, Any]]
    difficulty: int
    target_block_time: float
    block_times: List[float]
    adjustment_interval: int
    time_tolerance: float
    
    def __init__(self) -> None:
        """
        Initialize blockchain with genesis block and default parameters.
        """
        self.chain = []
        self.pending_transactions = []
        self.difficulty = 4
        self.target_block_time = 10
        self.block_times = []
        self.adjustment_interval = 10
        self.time_tolerance = 0.1
        self.create_genesis_block()

    def create_genesis_block(self) -> None:
        """
        Create and add the genesis block to the chain.
        """
        genesis_block = Block(
            index=0,
            transactions=[],
            timestamp=time.time(),
            previous_hash="0" * 64,
            difficulty=self.difficulty
        )
        genesis_block.mine_block()
        self.chain.append(genesis_block)

    def get_latest_block(self) -> Block:
        """
        Get the most recent block in the chain.
        
        Returns:
            Latest block in the chain
        """
        return self.chain[-1]

    @require(lambda self, transaction: isinstance(transaction, dict),
             "Transaction must be a dictionary.")
    @require(lambda self, transaction:
             "sender" in transaction and "recipient" in transaction,
             "Transaction must contain sender and recipient.")
    @ensure(lambda self, transaction:
            transaction in self.pending_transactions,
            "Transaction must be recorded in pending_transactions.")
    def add_transaction(self, transaction: Dict[str, Any]) -> None:
        """
        Add a new transaction to pending transactions.
        
        Args:
            transaction: Transaction data to add
        """
        self.pending_transactions.append(transaction)

    def adjust_difficulty(self) -> None:
        """
        Adjust mining difficulty based on recent block times.
        Updates difficulty if average block time deviates from target.
        """
        if len(self.block_times) < self.adjustment_interval:
            return
            
        avg_time = sum(self.block_times[-self.adjustment_interval:]) / self.adjustment_interval
        
        if avg_time > self.target_block_time * (1 + self.time_tolerance):
            self.difficulty = max(1, self.difficulty - 1)
        elif avg_time < self.target_block_time * (1 - self.time_tolerance):
            self.difficulty += 1
            
        self.block_times = []

    @require(lambda self:
             isinstance(self.pending_transactions, list),
             "pending_transactions must be a list.")
    @require(lambda self:
             len(self.pending_transactions) > 0,
             "There must be at least one pending transaction to mine.")
    @ensure(lambda self, result:
            result in self.chain,
            "Newly mined block must be appended to the chain.")
    @ensure(lambda self, result:
            self.pending_transactions == [],
            "pending_transactions should be cleared after mining.")
    def mine_pending_transactions(self) -> Block:
        """
        Mine pending transactions into a new block.
        
        Returns:
            Newly mined block
            
        Raises:
            ValueError: If no pending transactions
        """
        if not self.pending_transactions:
            raise ValueError("No pending transactions to mine")

        latest_block = self.get_latest_block()
        new_block = Block(
            index=latest_block.index + 1,
            transactions=self.pending_transactions,
            timestamp=time.time(),
            previous_hash=latest_block.hash,
            difficulty=self.difficulty
        )

        start_time = time.time()
        new_block.mine_block()
        block_time = time.time() - start_time
        self.block_times.append(block_time)
        self.adjust_difficulty()

        self.chain.append(new_block)
        self.pending_transactions = []
        return new_block

    @ensure(lambda self, result: isinstance(result, bool),
            "is_chain_valid must return a boolean value.")
    def is_chain_valid(self) -> bool:
        """
        Validate the entire blockchain.
        
        Returns:
            True if chain is valid, False otherwise
        """
        for i in range(1, len(self.chain)):
            current_block = self.chain[i]
            previous_block = self.chain[i-1]

            if current_block.hash != current_block.calculate_hash():
                return False

            if current_block.previous_hash != previous_block.hash:
                return False

            prefix = '0' * self.difficulty
            if not current_block.hash.startswith(prefix):
                return False

        return True
    
    @require(lambda self, index:
             0 <= index < len(self.chain),
             "Index must be within the range of the chain.")
    @ensure(lambda self, index, result:
            isinstance(result, dict)
            and "previous_link_ok" in result
            and "next_link_ok" in result,
            "Result must contain previous_link_ok and next_link_ok flags.")
    def verify_linkage(self, index: int) -> Dict[str, Any]:
        """
        Verify the linkage of block at the given index:
        - previous_link: True if this block’s previous_hash matches the prior block’s hash,
                        False if it does not, or None if this is the genesis block
        - next_link: True if the next block’s previous_hash matches this block’s hash,
                    False if it does not, or None if this is the chain tip
        Returns a dict with 'previous_link' and 'next_link'.
        """
        prev_ok = None
        next_ok = None

        # Check link to previous block
        if index > 0:
            prev_ok = (self.chain[index].previous_hash
                    == self.chain[index-1].hash)

        # Check link to next block
        if index < len(self.chain) - 1:
            next_ok = (self.chain[index+1].previous_hash
                    == self.chain[index].hash)

        return {
            'previous_link': prev_ok,
            'next_link': next_ok
        }

    def calculate_work(self) -> int:
        """
        Calculate the total work done in the blockchain.
        
        Returns:
            Total work done in the blockchain
        """
        return sum(int(block.hash, 16) for block in self.chain)

    def to_dict(self) -> Dict[str, Any]:
        """
        Convert blockchain to dictionary format.
        
        Returns:
            Dictionary containing blockchain data
        """
        return {
            "chain": [block.to_dict() for block in self.chain],
            "pending_transactions": self.pending_transactions,
            "difficulty": self.difficulty,
            "target_block_time": self.target_block_time,
            "adjustment_interval": self.adjustment_interval,
            "time_tolerance": self.time_tolerance
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'Blockchain':
        """
        Create blockchain instance from dictionary.
        
        Args:
            data: Dictionary containing blockchain data
            
        Returns:
            Blockchain instance
        """
        blockchain = object.__new__(cls)
        blockchain.chain = [Block.from_dict(block_data) for block_data in data['chain']]
        blockchain.pending_transactions = data['pending_transactions']
        blockchain.difficulty = data.get('difficulty', 4)
        blockchain.target_block_time = data.get('target_block_time', 10)
        blockchain.adjustment_interval = data.get('adjustment_interval', 10)
        blockchain.time_tolerance = data.get('time_tolerance', 0.1)
        blockchain.block_times = []
        return blockchain