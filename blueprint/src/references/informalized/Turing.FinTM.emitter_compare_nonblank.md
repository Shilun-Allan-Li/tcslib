<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_compare_nonblank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonblank Compared Entries

**Claim.** If $j<\max(|u|,|v|)$, then at least one of the entries of $u$ and $v$ at index $j$ exists.

**Proof.** Suppose both indexed entries are absent. A list has no entry at index $j$ exactly when its length is at most $j$, so both $|u|\le j$ and $|v|\le j$. Their maximum is then at most $j$, contradicting $j<\max(|u|,|v|)$.
