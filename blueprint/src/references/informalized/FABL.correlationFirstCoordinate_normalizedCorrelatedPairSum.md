<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Coordinate of the Normalized Pair Sum

**Claim.** For every natural number $n$ and every pair of sign vectors $x,y$ of length $n$, the first coordinate of their normalized correlated sum is $(\sqrt n)^{-1}\sum_{i=1}^n x_i$, with signs interpreted as real numbers.

**Proof.** Unfold the normalized pair sum, its coordinatewise encoding, and the correlated sign vectors. Taking the first coordinate of a scalar multiple multiplies the first coordinate by the scalar, and taking the first coordinate of a finite sum gives the sum of the first coordinates. Each encoded pair contributes the real value of $x_i$ in its first coordinate. The resulting first coordinate is therefore $(\sqrt n)^{-1}\sum_i \operatorname{signValue}(x_i)$.
