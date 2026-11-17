<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2BorrowPos_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Position Bound

**Claim.** For every binary word $u$, its borrow position is at most its length.

**Proof.** Induct on $u$. The empty word has borrow position and length both zero. For a word beginning with $1$, the borrow position is zero, so the bound is immediate. For a word beginning with $0$, its borrow position is one more than that of the tail; applying the inductive bound to the tail gives the desired inequality after adding one to both sides.
