<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.productSupNorm_toReal_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Supremum norm of a sign-valued function

**Claim.** For every Boolean function on the sign cube, the supremum norm of its real-valued sign representation is $1$.

**Proof.** Every value of the function is one of the two signs, so its real representation has absolute value $1$ everywhere. Consequently every value entering the finite supremum is $1$, giving an upper bound of $1$. For the reverse inequality, choose any point of the cube, for example the constant-one point. Its represented value has absolute value $1$, and the pointwise bound by the supremum (`abs_le_productSupNorm`) shows that the supremum is at least $1$. The two bounds give equality.

**Key facts.** `FABL.abs_le_productSupNorm`.
