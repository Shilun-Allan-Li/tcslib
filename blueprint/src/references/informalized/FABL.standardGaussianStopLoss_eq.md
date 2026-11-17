<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianStopLoss_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian stop-loss identity

**Claim.** For every real $t$, the expected positive part of a standard Gaussian variable minus $t$ equals its density at $t$ minus $t$ times its upper-tail probability at $t$.

**Proof.** Express the expectation as an integral against the standard Gaussian density. The positive part $(x-t)^+$ vanishes for $x\le t$ and equals $x-t$ for $x>t$, so the integral reduces to the upper half-line integral of the density times $x-t$. Split this into the integral of $x$ times the density minus $t$ times the integral of the density. The first upper-tail moment is the density at the threshold (\texttt{integral\_Ioi\_mul\_standardGaussianDensity}); the upper-tail integral of the density is the upper-tail probability (\texttt{integral\_Ioi\_standardGaussianDensity}). Substitution yields the asserted identity.

**Key facts.** `FABL.integral_Ioi_mul_standardGaussianDensity`, `FABL.integral_Ioi_standardGaussianDensity`.
