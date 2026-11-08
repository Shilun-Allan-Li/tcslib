<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productCovariance_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Covariance equals variance

**Claim.** The covariance of $f$ with itself equals the variance of $f$.

**Proof.** Unfold covariance and variance. In both expressions the integrand is the square of the centered function: for every point $x$, $(f(x)-\mathbb E f)(f(x)-\mathbb E f)=(f(x)-\mathbb E f)^2$. Their expectations are therefore equal.
