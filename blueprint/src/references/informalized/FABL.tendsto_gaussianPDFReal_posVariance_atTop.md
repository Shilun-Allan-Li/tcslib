<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_gaussianPDFReal_posVariance_atTop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian density vanishes at positive infinity

**Claim.** For every real mean $\mu$ and every positive variance $v$, the Gaussian density at $x$ tends to zero as $x$ tends to positive infinity.

**Proof.** Write the density as $\bigl(\sqrt{2\pi v}\bigr)^{-1}\exp\!\left(-\frac{(y-\mu)^2}{2v}\right)$. As $y\to+\infty$, the shift $y-\mu$ also tends to positive infinity, so its square tends to positive infinity. Since $2v>0$, multiplying that square by $-1/(2v)$ sends it to negative infinity. The exponential therefore tends to zero. The prefactor is a fixed finite constant, so multiplying by it leaves the limit zero.
