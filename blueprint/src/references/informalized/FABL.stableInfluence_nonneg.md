<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.stableInfluence_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Stable Influence

**Claim.** For every $\rho\in[0,1]$, function $f$ and coordinate $i$, the stable influence of $f$ at parameter $\rho$ and coordinate $i$ is nonnegative.

**Proof.** Expand the stable influence as a sum over coordinate subsets $S$ containing $i$. Each summand is the product of $\rho^{|S|-1}$ and a squared Fourier coefficient. Since $\rho\ge0$, its natural-number power is nonnegative, and the square is nonnegative. Thus every summand is nonnegative, so their finite sum is nonnegative.
