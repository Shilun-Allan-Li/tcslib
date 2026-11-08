<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.spaceUsedWith_le_of_ranges -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound from Choice-Run Intervals

**Claim.** If every run under a choice word of length at most $|w|$ keeps each tape head inside its specified integer interval, then the total number of distinct cells visited along the run under $w$ is at most the sum of the interval lengths in cells.

**Proof.** For each tape, every visited position is the head position after some prefix of the choice word $w$. Such a prefix has length at most $|w|$, so the assumed bounds place every visited position in the integer interval $[\mathrm{lo}(i),\mathrm{hi}(i)]$. Hence the visited-position set is a subset of that interval, and its cardinality is no larger than the interval's cardinality. The integer interval contains $\mathrm{hi}(i)-\mathrm{lo}(i)+1$ integers; summing these per-tape bounds gives the claimed total-space estimate.
