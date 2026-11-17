<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBorrowPos_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Initial False Segment

**Claim.** For every finite Boolean word $u$, the length of its initial segment of false entries is at most $|u|$.

**Proof.** Induct on the word. The empty word has initial false-segment length zero. For a nonempty word, if its first entry is true, the initial false segment has length zero. If its first entry is false, its length is one plus the initial false-segment length of the tail; by induction that is at most one plus the tail's length, which is the length of the whole word.
