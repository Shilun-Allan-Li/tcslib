<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLInfinityNorm_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the supremum norm

**Claim.** For a finite nonempty set $\Omega$ and a function $f:\Omega\to\mathbb R$, the supremum norm of $f$ is nonnegative.

**Proof.** Choose any point $x\in\Omega$, which exists because the domain is nonempty. The supremum of $|f|$ is at least $|f(x)|$, and an absolute value is nonnegative. Hence the supremum norm is nonnegative.
