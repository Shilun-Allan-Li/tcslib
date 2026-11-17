<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.NDTM.spaceUsedWith_le_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Space Under Appending Choices

**Claim.** Appending a choice word cannot decrease the total number of distinct work-tape cells visited.

**Proof.** Fix a work tape and take any cell visited during the run under $w$. It is the head position at some prefix time $j\le |w|$. The first $j$ choices of $w w'$ are exactly the first $j$ choices of $w$, so the same position occurs among the prefix positions visited under the concatenated word. Thus the visited-position set for $w$ is contained in the one for $w w'$, and its cardinality is no larger. Summing this inequality over the work tapes proves the inequality for total space usage.
