<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.standardGaussianUpperTail_eq_anchor_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Tail Integral from Zero

**Claim.** For every real number $t$, the standard Gaussian upper-tail probability at $t$ equals its value at $0$ minus the oriented integral of the standard Gaussian density from $0$ to $t$.

**Proof.** Express the upper tail at both $t$ and $0$ as the integral of the standard Gaussian density over the corresponding open rays, using the upper-tail integral identity (`standardGaussianUpperTail_eq_integral_Ioi`). The difference between these two ray integrals is the oriented interval integral from $0$ to $t$: the interval-integral subtraction formula gives this for either order of the endpoints, including when $t<0$. Rearranging yields the stated identity.

**Key facts.** `FABL.standardGaussianUpperTail_eq_integral_Ioi`.
