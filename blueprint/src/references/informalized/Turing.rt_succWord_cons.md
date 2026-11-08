<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_succWord_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Word for a Leading One

**Claim.** For every Boolean word $w$, the successor word of the word formed by placing a one before $w$ is a zero followed by the successor word of $w$.

**Proof.** Unfold the successor word, which uses the fixed-width increment when that increment is defined and otherwise supplies a word of zeros followed by one. Split according to whether incrementing $w$ succeeds. If it succeeds, its first bit is either zero or one; the recursive definition of the fixed-width increment shows that placing a one before $w$ causes a carry, producing an initial zero and the incremented remainder. If it overflows, the fallback word has one more zero than the fallback for $w$, so it too is a zero followed by the successor word of $w$. In both cases the lists agree entry by entry.
