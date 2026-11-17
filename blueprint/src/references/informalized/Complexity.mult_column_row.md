<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_column_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A single multiplication column

**Claim.** The sum over positions $q$ of the contribution from bit $t$ is zero when $p>j$, and otherwise is exactly $t b_{j-p}$, with out-of-range bits interpreted as zero.

**Proof.** If $p>j$, then $p+q=j$ is impossible for every nonnegative $q$, so every summand vanishes. Now suppose $p\le j$. The only possible nonzero summand has $q=j-p$. If this index lies in the range of the string, the sum has exactly that one contribution, namely $t b_{j-p}$. If it lies beyond the string, the bit at that index is zero by the out-of-range convention, and every summand vanishes. These cases give the stated formula.
