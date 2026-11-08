<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.totalInfluence_dimension_one_eq_two_mul_noiseSensitivity_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence and noise sensitivity in dimension one

**Claim.** For every Boolean function on the one-dimensional cube, its total influence equals twice its noise sensitivity at noise rate $1/2$.

**Proof.** Express total influence as the sum over levels $k$ of $k$ times the Fourier weight at level $k$ (FABL.totalInfluence_eq_sum_level_mul_fourierWeight). The noise sensitivity formula expresses the same level weights with coefficient $\frac12(1-(1-2\delta)^k)$ (FABL.noiseSensitivity_eq_sum_level). In dimension one, only levels $0$ and $1$ occur. At $\delta=1/2$, the level-zero coefficient vanishes and the level-one coefficient is $1/2$. Thus twice the noise sensitivity is exactly the level-one Fourier weight, which is also the total influence.

**Key facts.** `FABL.totalInfluence_eq_sum_level_mul_fourierWeight`, `FABL.noiseSensitivity_eq_sum_level`.
