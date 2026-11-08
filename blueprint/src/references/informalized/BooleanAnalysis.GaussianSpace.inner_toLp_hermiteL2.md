<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.inner_toLp_hermiteL2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Coefficient as an Inner Product

**Claim.** The inner product of the $L^2$ class of $f$ with the $L^2$ class of the normalized multivariate Hermite function indexed by $\alpha$ equals the Hermite coefficient of $f$.

**Proof.** Real inner products are symmetric, so reverse the order of the two classes. The identity \texttt{inner_hermiteL2_toLp} then identifies this inner product with the integral defining the Hermite coefficient.

**Key facts.** `BooleanAnalysis.GaussianSpace.inner_hermiteL2_toLp`.
