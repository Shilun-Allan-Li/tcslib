<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.prod_boolToSign_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Products Under Coordinate Identification

**Claim.** The product of sign encodings over source indices in $S$ equals the product over target indices whose fibers in $S$ have odd size.

**Proof.** Group the source product by the value of $\pi(i)$. In the fiber over each target index $j$, every factor is the same sign $\sigma(w_j)$, so that fiber contributes $\sigma(w_j)^{r_j}$, where $r_j$ is its size. A sign is either $1$ or $-1$, so this power equals the sign itself when $r_j$ is odd and equals $1$ when $r_j$ is even (\texttt{boolToSign_pow}). Multiplying over target indices therefore leaves precisely the factors indexed by the odd-sized fibers, as claimed.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.boolToSign_pow`.
