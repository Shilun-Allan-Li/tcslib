<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_borrow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Scan Run

**Claim.** Starting in phase $8$ with counter word $v w$ and head at $|v|$, the host runs for one step per scanned bit plus one exit step, producing the decrement result and the corresponding phase and head position described in the statement.

**Proof.** Induct on $w$, keeping the prefix $v$ arbitrary. If $w$ is empty, the one-step borrow rule detects the blank cell and exits to phase $10$, with the head at $|v|-1$. If $w$ begins with true, the borrow rule changes that bit to false and enters phase $9$; this is exactly the decrement result, and the scan stops after that single step. If $w$ begins with false, the rule changes it to true, moves the head one cell right, and remains in phase $8$. Apply the induction hypothesis to the remaining suffix with the enlarged prefix $v$ followed by true. The run-length recursion shifts the remaining number of steps by one, while list associativity and integer arithmetic identify the final counter contents and head position with the stated result.

**Key facts.** `Turing.FinTM.loopHost_borrow_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
