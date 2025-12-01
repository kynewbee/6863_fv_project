----------------------- MODULE VotingSystem -----------------------
EXTENDS Integers, Sequences, FiniteSets

(* CONSTANTS: 
   Voters: The set of all eligible voters.
   Candidates: The set of available candidates.
*)
CONSTANTS Voters, Candidates

(* VARIABLES:
   chain: The blockchain, modeled as a sequence of blocks (sets of transactions).
   mempool: The memory pool, storing pending votes before they are mined.
   voted_users: A set tracking users who have already cast a vote.
*)
VARIABLES chain, mempool, voted_users

vars == <<chain, mempool, voted_users>>

(* TypeOK: The Type Invariant.
   Ensures that variables always hold values of the correct data types.
*)
TypeOK ==
    /\ chain \in Seq(SUBSET [voter : Voters, candidate : Candidates])
    /\ mempool \in SUBSET [voter : Voters, candidate : Candidates]
    /\ voted_users \in SUBSET Voters

-------------------------------------------------------------------
(* Initial State: 
   The system starts with an empty chain (or a genesis block), 
   an empty mempool, and no recorded voters.
*)
Init ==
    /\ chain = << {} >> 
    /\ mempool = {}
    /\ voted_users = {}

-------------------------------------------------------------------
(* Action 1: UserVotes
   Represents a user casting a vote.
   Pre-condition: The user (u) must not be in the 'voted_users' set.
   Post-condition: The vote is added to the mempool, and the user is marked as voted.
*)
UserVotes(u, c) ==
    /\ u \notin voted_users
    /\ mempool' = mempool \cup {[voter |-> u, candidate |-> c]}
    /\ voted_users' = voted_users \cup {u}
    /\ chain' = chain

(* Action 2: MineBlock
   Represents the mining process.
   Pre-condition: The mempool must not be empty.
   Post-condition: All transactions in the mempool are appended as a new block 
                   to the chain, and the mempool is cleared.
*)
MineBlock ==
    /\ mempool /= {}
    /\ chain' = Append(chain, mempool)
    /\ mempool' = {}
    /\ voted_users' = voted_users

-------------------------------------------------------------------
(* Next: The state transition relation.
   The system advances by either a user voting OR a block being mined.
*)
Next ==
    \/ (\E u \in Voters, c \in Candidates : UserVotes(u, c))
    \/ MineBlock
    \/ UNCHANGED vars

(* Spec: The temporal specification of the system. *)
Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------
(* Safety Property: NoDoubleVoting
   Invariant: It ensures that for any user marked as 'voted', 
   there are no duplicate entries for that user in the current mempool.
   (Note: In a full model, this would also check the entire chain history).
*)
NoDoubleVoting == 
    \A u \in Voters : 
        (u \in voted_users) => 
        (\A v1, v2 \in mempool : (v1.voter = u /\ v2.voter = u) => v1 = v2)

-------------------------------------------------------------------
===================================================================