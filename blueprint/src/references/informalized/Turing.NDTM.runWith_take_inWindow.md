<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.runWith_take_inWindow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs Remain Within a Space Window

**Claim.** If the space used by the run on $x$ under $w$ is at most $s$, then every configuration reached under a prefix of $w$ has work-tape head positions of absolute value at most $s$, and all cells at positions of absolute value greater than $s$ are blank.

**Proof.** Fix a tape and a position visited during the run under the prefix in question. The visited positions for that prefix form a subset of those visited during the full run (`Turing.NDTM.visitedWith_take_subset`). The number of full-run visited positions on this tape is at most the total space, hence at most $s$, since each tape's cardinality is one nonnegative summand of that total. The bound on a visited position (`Turing.NDTM.abs_lt_card_visitedWith`) now gives absolute value strictly less than that cardinality, and therefore at most $s$. The current head position is among the visited positions, by taking the prefix length equal to the length of the truncated choice word. Finally, if a cell outside the radius-$s$ window were nonblank in the reached configuration, it would itself be visited (`Turing.NDTM.mem_visitedWith_of_ne_none`); the bound just proved would contradict its absolute value being greater than $s$.

**Key facts.** `Turing.NDTM.visitedWith_take_subset`, `Turing.NDTM.abs_lt_card_visitedWith`, `Turing.NDTM.mem_visitedWith_of_ne_none`.
