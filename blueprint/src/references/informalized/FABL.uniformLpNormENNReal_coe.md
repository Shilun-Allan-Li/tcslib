<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLpNormENNReal_coe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-exponent norm under coercion

**Claim.** For a finite set $\Omega$, a nonnegative real number $q$, and a function $f:\Omega\to\mathbb R$, the extended-exponent uniform norm at the coercion of $q$ to the extended nonnegative reals equals the uniform $q$-norm.

**Proof.** The coercion of a finite nonnegative real number into the extended nonnegative reals is finite, so it is not $\infty$. The definition of the extended-exponent norm therefore selects the finite-exponent branch. The coerced exponent's real value is exactly $q$, giving the uniform $q$-norm.
