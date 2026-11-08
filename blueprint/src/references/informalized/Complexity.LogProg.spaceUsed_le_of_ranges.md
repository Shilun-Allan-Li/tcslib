<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean :: Complexity.LogProg.spaceUsed_le_of_ranges -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound from Head-Position Intervals

**Claim.** If every head position through time $T$ lies in its specified interval, then the total number of distinct work-tape cells visited through time $T$ is at most the sum of the interval lengths in cells.

**Proof.** On each tape, the visited cells are precisely head positions at times in the finite range from $0$ through $T$. Each such time satisfies the assumed head-position bounds, so the visited set is contained in $[\mathrm{lo}(i),\mathrm{hi}(i)]$. Its cardinality is therefore at most the number of integers in that interval, namely $\mathrm{hi}(i)-\mathrm{lo}(i)+1$. Summing over tapes yields the asserted bound.
