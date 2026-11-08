<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopBorrowPos_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Borrow Scan

**Claim.** For every Boolean word $u$, the length of its maximal initial string of false bits is at most the length of $u$.

**Proof.** Induct on the word. The empty word has scan length and word length both zero. For a word $b::u$, if $b$ is true, the initial false string is empty, so the bound is immediate. If $b$ is false, its scan length is one plus the scan length of $u$; by induction this is at most $1+|u|$, which is the length of $b::u$.
