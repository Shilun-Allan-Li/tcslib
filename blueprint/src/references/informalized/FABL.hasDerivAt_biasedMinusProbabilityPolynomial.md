<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.hasDerivAt_biasedMinusProbabilityPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the biased minus-probability polynomial

**Claim.** For $p\in(0,1)$, the biased minus-probability polynomial is differentiable at $p$, with derivative $\sigma(p)^{-1}\sum_i\widehat{f_{\mathbb R}}_p(\{i\})$.

**Proof.** The bias mean $t\mapsto 1-2t$ has derivative $-2$. Compose the derivative formula for the biased expectation polynomial at the bias mean (`FABL.hasDerivAt_biasedExpectationPolynomial_eq_singletons`) with this affine map. The minus-probability polynomial is one half of one minus that composition, so the chain rule and the factor $-1/2$ multiply the derivative by $(-1/2)(-2)=1$. The resulting derivative is exactly the stated singleton-coefficient expression.

**Key facts.** `FABL.hasDerivAt_biasedExpectationPolynomial_eq_singletons`.
