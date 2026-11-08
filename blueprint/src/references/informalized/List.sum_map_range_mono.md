<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.sum_map_range_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Initial Range Sums

**Claim.** If $a\le b$, then the sum of the natural-number values $g(i)$ for $i<a$ is at most the corresponding sum for $i<b$.

**Proof.** Write $b=a+c$ for some natural number $c$. The range up to $b$ splits into the range up to $a$ followed by the next $c$ indices. Mapping $g$ preserves this concatenation, and the sum of the concatenation is the sum up to $a$ plus the sum of the additional terms. Since those terms are natural numbers, their sum is nonnegative, so adding it cannot decrease the original sum.
