import hashlib
import json
import time
from typing import List, Dict, Any, Tuple

from icontract import require, ensure

def hash_pair(a: str, b: str) -> str:
    """
    Calculate combined hash of two hash values.
    
    Args:
        a: First hash string
        b: Second hash string
    
    Returns:
        Combined hash string
    """
    return hashlib.sha256((a + b).encode()).hexdigest()

@require(lambda tx_hashes: tx_hashes is not None)
@require(lambda tx_hashes:
         all(isinstance(h, str) for h in tx_hashes),
         "All transaction hashes must be strings.")
@ensure(lambda tx_hashes, result:
        isinstance(result, str) and len(result) == 64,
        "Merkle root must be a 64-character hex string.")
def compute_merkle_root(tx_hashes: List[str]) -> str:
    """
    Calculate Merkle root hash from transaction hashes.
    
    Args:
        tx_hashes: List of transaction hash strings
    
    Returns:
        Merkle root hash string
    """
    if not tx_hashes:
        return '0' * 64
    if len(tx_hashes) == 1:
        return tx_hashes[0]
    
    new_level = []
    for i in range(0, len(tx_hashes), 2):
        left = tx_hashes[i]
        right = tx_hashes[i+1] if i+1 < len(tx_hashes) else left
        new_level.append(hash_pair(left, right))
    return compute_merkle_root(new_level)

class Block:
    """
    Block class representing a block in the blockchain.
    Contains transactions, timestamp, and cryptographic hashes.
    """

    index: int
    transactions: List[Dict[str, Any]]
    previous_hash: str
    timestamp: float
    difficulty: int
    nonce: int
    hash: str
    merkle_root: str
    merkle_tree: List[List[str]]
    
    def __init__(self, index: int, transactions: List[Dict[str, Any]], 
                 previous_hash: str, timestamp: float = None, difficulty: int = 2)-> None:
        """
        Initialize a new block.
        
        Args:
            index: Block index in the chain
            transactions: List of transaction dictionaries
            previous_hash: Hash of the previous block
            timestamp: Block creation timestamp
            difficulty: Mining difficulty level
        """
        self.index = index
        self.transactions = transactions
        self.timestamp = timestamp or time.time()
        self.previous_hash = previous_hash
        self.difficulty = difficulty
        self.nonce = 0
        
        # Store Merkle tree nodes
        self.merkle_tree = self._build_merkle_tree()
        self.merkle_root = self.merkle_tree[-1][0]  # Root is the last level's first node
        self.hash = self.calculate_hash()

    def _build_merkle_tree(self) -> List[List[str]]:
        """
        Build complete Merkle tree and store all levels.
        
        Returns:
            List of lists, where each inner list represents a level in the tree
        """
        if not self.transactions:
            return [['0' * 64]]
            
        # Calculate leaf node hashes
        tx_hashes = [
            hashlib.sha256(json.dumps(tx, sort_keys=True).encode()).hexdigest()
            for tx in self.transactions
        ]
        
        # Build tree level by level
        tree = [tx_hashes]  # First level is transaction hashes
        current_level = tx_hashes
        
        while len(current_level) > 1:
            next_level = []
            for i in range(0, len(current_level), 2):
                left = current_level[i]
                right = current_level[i+1] if i+1 < len(current_level) else left
                next_level.append(hash_pair(left, right))
            tree.append(next_level)
            current_level = next_level
            
        return tree

    def calculate_hash(self) -> str:
        """Calculate block hash"""
        block_string = json.dumps({
            "index": self.index,
            "previous_hash": self.previous_hash,
            "timestamp": self.timestamp,
            "nonce": self.nonce,
            "transactions": self.transactions  # Use transactions instead of merkle_root
        }, sort_keys=True)
        return hashlib.sha256(block_string.encode()).hexdigest()

    @require(lambda self: isinstance(self.difficulty, int) and self.difficulty > 0,
             "Difficulty must be a positive integer.")
    @ensure(lambda self:
            isinstance(self.hash, str)
            and self.hash.startswith('0' * self.difficulty),
            "Mined hash must satisfy the difficulty prefix.")
    def mine_block(self) -> None:
        """
        Mine block by finding nonce that satisfies difficulty requirement.
        Updates block hash and nonce.
        """
        prefix = '0' * self.difficulty

        if not hasattr(self, "hash") or not isinstance(self.hash, str):
            self.hash = self.calculate_hash()

        while not self.hash.startswith(prefix):
            self.nonce += 1
            self.hash = self.calculate_hash()

    def edit_transaction(self, tx_index: int, field: str = None, new_value: Any = None, new_transaction: Dict[str, Any] = None) -> tuple:
        """
        Edit a transaction in the block.
        
        Args:
            tx_index: Index of transaction to edit
            field: Field to modify (optional)
            new_value: New value for the field (optional)
            new_transaction: New transaction to replace (optional)
            
        Returns:
            tuple: (original_transaction, original_merkle_root)
        """
        if tx_index >= len(self.transactions):
            raise IndexError("Transaction index out of range")
            
        # Store original values
        original_tx = self.transactions[tx_index].copy()
        original_merkle = self.merkle_root
        
        # Modify transaction
        if field is not None and new_value is not None:
            self.transactions[tx_index][field] = new_value
        elif new_transaction is not None:
            self.transactions[tx_index] = new_transaction
            
        # Update block hash and merkle root
        self.merkle_tree = self._build_merkle_tree()
        self.merkle_root = self.merkle_tree[-1][0]  # Root is the last level's first node
        self.hash = self.calculate_hash()
        
        return original_tx, original_merkle

    @ensure(
        lambda self, result:
        isinstance(result, dict)
        and {"merkle_ok", "hash_ok", "expected_merkle_root", "expected_hash"} <= result.keys(),
        "verify_self must return a dict with the required keys."
    )
    @ensure(
        lambda self, result:
        isinstance(result["merkle_ok"], bool) and isinstance(result["hash_ok"], bool),
        "merkle_ok and hash_ok must be boolean flags."
    )
    def verify_self(self) -> Dict[str, Any]:
        """
        Verify the internal integrity of this block:
        - Check that merkle_root matches the hash of transactions
        - Check that hash matches the block header (including merkle_root)
        Returns a dict containing:
        - merkle_ok: whether the stored merkle_root is correct
        - hash_ok: whether the stored hash is correct
        - expected_merkle_root: the merkle root recomputed from transactions
        - expected_hash: the hash recomputed from block header
        """
        # Rebuild merkle tree and get root
        new_tree = self._build_merkle_tree()
        expected_merkle = new_tree[-1][0]  # Root is the last level's first node
        expected_hash = self.calculate_hash()
        
        return {
            'merkle_ok': self.merkle_root == expected_merkle,
            'hash_ok': self.hash == expected_hash,
            'expected_merkle_root': expected_merkle,
            'expected_hash': expected_hash
        }
    
    def verify_transaction(self, tx_index: int) -> Dict[str, Any]:
        """
        Verify if a specific transaction has been modified using stored Merkle tree.
        
        Args:
            tx_index: Index of the transaction to verify
            
        Returns:
            Dict containing:
            - is_valid: Whether the transaction is valid
            - tx_hash: Current hash of the transaction
            - proof: Merkle proof for verification
            - merkle_root: Current Merkle root
            - modified_path: Path to the modified node if found
        """
        if tx_index >= len(self.transactions):
            raise IndexError("Transaction index out of range")
            
        # Calculate current transaction hash
        current_tx_hash = hashlib.sha256(
            json.dumps(self.transactions[tx_index], sort_keys=True).encode()
        ).hexdigest()
        
        # Get path to root
        path = self._get_path_to_root(tx_index)
        
        # Verify path and find modified node
        modified_path = []
        current_hash = current_tx_hash
        current_index = tx_index
        
        for level in range(len(self.merkle_tree) - 1):
            if current_index % 2 == 0:
                # Current node is left child
                sibling_index = current_index + 1
                if sibling_index < len(self.merkle_tree[level]):
                    sibling_hash = self.merkle_tree[level][sibling_index]
                    current_hash = hash_pair(current_hash, sibling_hash)
                else:
                    # Handle odd number of nodes
                    current_hash = hash_pair(current_hash, current_hash)
            else:
                # Current node is right child
                sibling_hash = self.merkle_tree[level][current_index - 1]
                current_hash = hash_pair(sibling_hash, current_hash)
            
            # Check if this level's hash matches stored tree
            expected_hash = self.merkle_tree[level + 1][current_index // 2]
            if current_hash != expected_hash:
                modified_path.append({
                    'level': level,
                    'index': current_index,
                    'computed_hash': current_hash,
                    'expected_hash': expected_hash
                })
            
            current_index = current_index // 2
        
        return {
            'is_valid': current_hash == self.merkle_root,
            'tx_hash': current_tx_hash,
            'merkle_root': self.merkle_root,
            'computed_root': current_hash,
            'modified_path': modified_path,
            'transaction': self.transactions[tx_index]
        }

    def _get_path_to_root(self, tx_index: int) -> List[Tuple[int, int]]:
        """
        Get path from transaction to root in Merkle tree.
        
        Args:
            tx_index: Index of the transaction
            
        Returns:
            List of (level, index) tuples representing the path
        """
        path = []
        current_index = tx_index
        
        for level in range(len(self.merkle_tree) - 1):
            path.append((level, current_index))
            current_index = current_index // 2
            
        return path

    def to_dict(self) -> Dict[str, Any]:
        """
        Convert block to dictionary format.
        
        Returns:
            Dictionary containing block data
        """
        return {
            "index": self.index,
            "transactions": self.transactions,
            "timestamp": self.timestamp,
            "previous_hash": self.previous_hash,
            "hash": self.hash,
            "nonce": self.nonce,
            "difficulty": self.difficulty,
            "merkle_root": self.merkle_root,
            "merkle_tree": self.merkle_tree
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'Block':
        """
        Create block instance from dictionary.
        
        Args:
            data: Dictionary containing block data
            
        Returns:
            Block instance
        """
        block = cls(
            index=data["index"],
            transactions=data["transactions"],
            previous_hash=data["previous_hash"],
            timestamp=data["timestamp"],
            difficulty=data.get("difficulty", 2)
        )
        block.hash = data["hash"]
        block.nonce = data["nonce"]
        block.merkle_root = data.get("merkle_root", '0' * 64)
        block.merkle_tree = data.get("merkle_tree", [['0' * 64]])
        return block