<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/ContinuousBounds.lean :: BooleanAnalysis.GaussianSpace.toReal_eLpNorm_ofReal_eq_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral formula for the real $L^p$ norm

**Claim.** If $p>0$ and $f\in L^p(\mu)$, then the real-valued $L^p$ norm equals $\left(\int_X |f(x)|^p\,d\mu(x)\right)^{1/p}$.

**Proof.** The eLp norm formula for an $L^p$ function expresses its eLp norm as the appropriate power of the integral of the norm of $f$. Apply this formula at exponent $p$, which is permitted because $p>0$ ensures the exponent is positive and finite. For real-valued $f$, its pointwise norm is $|f|$. Converting the resulting nonnegative extended-real quantity to a real number gives the ordinary integral expression, and rewriting the reciprocal exponent as $1/p$ yields the claimed formula.
