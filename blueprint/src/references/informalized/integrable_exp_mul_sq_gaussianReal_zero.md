<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean :: integrable_exp_mul_sq_gaussianReal_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian quadratic exponential integrability

**Claim.** If $v>0$ and $2tv<1$, then $y\mapsto e^{ty^2}$ is integrable with respect to the centered Gaussian of variance $v$.

**Proof.** Rewrite the Gaussian measure as Lebesgue measure weighted by its density. The density-weighted integrand simplifies to a constant multiple of $\exp\!\bigl(-(1/(2v)-t)y^2\bigr)$. The condition $2tv<1$, together with $v>0$, implies $1/(2v)-t>0$. The function $y\mapsto e^{-b y^2}$ is integrable over the real line for every $b>0$; multiplying it by a finite constant preserves integrability. The pointwise identity between the rewritten and original integrands transfers integrability back to the original expression.
