<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersNorm_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power identity for the Gowers norm

**Claim.** For positive $k$, the $2^k$-th power of the Gowers norm equals the diagonal Gowers inner product.

**Proof.** Write $k=r+1$ using positivity of $k$. The diagonal inner product at this order is nonnegative (`gowersDiagonalInner_nonneg`). By definition the norm is that inner product raised to the reciprocal of the integer $2^k$. For a nonnegative real base, raising to this reciprocal power and then to the integer power recovers the base. This gives the asserted identity.

**Key facts.** `FABL.gowersDiagonalInner_nonneg`.
