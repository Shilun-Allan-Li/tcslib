<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.spaceUsedWith_le_of_haltsWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bound from a halting time bound

**Claim.** If all choice words of length exactly $T$ halt and use at most $S$ work-tape cells, then every choice word, of any length, uses at most $S$ cells.

**Proof.** Fix a choice word $w$. If $|w|\leq T$, append $T-|w|$ arbitrary choice bits to obtain a word of length $T$. Space used cannot decrease when a run is extended (`spaceUsedWith_le_append`), so the space used by $w$ is at most that of the padded word, which is at most $S$ by hypothesis. If $|w|>T$, split it after its first $T$ bits. The run on that prefix halts by hypothesis, and the space used after a halted run is unchanged by any appended choices (`spaceUsedWith_append_of_halt`). Hence $w$ uses exactly the space used by its length-$T$ prefix, at most $S$.

**Key facts.** `Turing.NDTM.spaceUsedWith_le_append`, `Turing.NDTM.spaceUsedWith_append_of_halt`.
