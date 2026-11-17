<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_clean_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Simulation Bounds

**Claim.** If the machine computes $y$ from $x$ in $t$ steps using at most $s$ work-tape cells, its clean simulation has a halting time with output $y$, blank work tapes, and every work-tape head at the origin; throughout the run, all head positions have absolute value at most $s$.

**Proof.** The computation hypothesis gives both that the original machine is halted at time $t$ and that its output then equals $y$ (`Turing.FinTM.computesInTime_iff`). For each work tape, its number of visited head positions is at most the total space used, by the per-tape space bound (`Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed`). The cleaning theorem (`Complexity.LogProg.cleanTM_run`), applied with these per-tape bounds, supplies a time at which the clean simulation is halted, has the same output as the original run, has blank work tapes and all heads at the origin, and satisfies the head-position bound at every time through that endpoint. The output equality identifies the clean simulation's output as $y$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed`, `Complexity.LogProg.cleanTM_run`.
