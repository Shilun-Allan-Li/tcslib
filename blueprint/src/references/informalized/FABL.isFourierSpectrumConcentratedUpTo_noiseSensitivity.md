<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.isFourierSpectrumConcentratedUpTo_noiseSensitivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Sensitivity Bounds High-Degree Weight

**Claim.** For a Boolean function and $0<\delta\le 1/2$, the Fourier weight on degrees greater than $1/\delta$ is at most $\frac{2}{1-e^{-2}}$ times its noise sensitivity at rate $\delta$.

**Proof.** Set $c=1-e^{-2}$, which is positive. For every set $S$ of degree greater than $1/\delta$, the power bound gives $(1-2\delta)^{|S|}\le e^{-2}$, so $c\le 1-(1-2\delta)^{|S|}$. Multiplying by the nonnegative squared Fourier coefficient and summing over these high-degree sets bounds $c$ times their total weight by the sum over all sets of $(1-(1-2\delta)^{|S|})$ times the squared coefficient. Extending to all sets is valid because these factors are nonnegative. The Fourier formula for twice the noise sensitivity identifies that full sum with twice the noise sensitivity. Dividing by the positive constant $c$ yields the claimed bound.

**Key facts.** `FABL.one_sub_two_mul_pow_le_exp_neg_two`, `FABL.one_sub_one_sub_two_mul_pow_nonneg`, `FABL.two_mul_noiseSensitivity_eq_sum_fourier`.
