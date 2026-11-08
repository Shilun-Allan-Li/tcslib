<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformLpNorm_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the uniform norm

**Claim.** For a finite set $\Omega$, any real $p$, and any function $f:\Omega\to\mathbb R$, the uniform $L^p$ norm of $f$ is nonnegative.

**Proof.** Unfold the definition. For each $x$, the real power $|f(x)|^p$ is nonnegative because its base is nonnegative. Its uniform mean is therefore nonnegative, and a real power of a nonnegative base is nonnegative for every real exponent. This gives the claim.
