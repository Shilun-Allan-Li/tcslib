<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.sum_normalizedCoefficient_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of squared normalized coefficients

**Claim.** For every positive natural number $n$, the sum over the $n$ coordinates of the squares of $1/\sqrt n$ equals $1$.

**Proof.** There are $n$ identical summands, each equal to $1/n$, since squaring the reciprocal square root gives the reciprocal of $n$. Their sum is therefore $n\cdot(1/n)=1$. The positivity assumption ensures the square root is nonzero, so this reciprocal calculation is valid.
