<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.noiseOp_snoc_slice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factoring Noise Across the Last Coordinate

**Claim.** Applying noise on the $(n+1)$-dimensional cube is equivalent to first applying noise to each restriction at the last coordinate and then applying one-dimensional noise to the resulting function of that coordinate.

**Proof.** Write a point of the one-dimensional cube as the concatenation of the unique zero-dimensional point and its bit. The formula for noise after appending a bit (`BooleanAnalysis.Hypercontractivity.noiseOp_snoc`) expresses the left side as the noise of the average of the two last-coordinate restrictions plus the sign of the bit times $\rho$ times the noise of their difference. On the right, apply the same formula to the outer one-bit noise. The inner zero-dimensional noise operators are identities (`BooleanAnalysis.Hypercontractivity.noiseOp_dim_zero`), so the two restrictions remain unchanged. Their average and difference have Fourier coefficients equal, respectively, to the half-sum and half-difference of the restriction coefficients (`BooleanAnalysis.Hypercontractivity.fourierCoeff_avgLast_restrictions`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_diffLast_restrictions`). Substituting these expressions into the Fourier sums and collecting terms gives the same average-plus-signed-difference expression on both sides.

**Key facts.** `BooleanAnalysis.Hypercontractivity.noiseOp_snoc`, `BooleanAnalysis.Hypercontractivity.noiseOp_dim_zero`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_avgLast_restrictions`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_diffLast_restrictions`.
