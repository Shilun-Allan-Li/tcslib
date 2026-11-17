<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersNorm_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Gowers norm

**Claim.** For positive $k$, the Gowers norm of any real-valued function on the Boolean cube is nonnegative.

**Proof.** Since $k>0$, write $k=r+1$ for some nonnegative integer $r$. The diagonal inner product at order $r+1$ is nonnegative (`gowersDiagonalInner_nonneg`). The Gowers norm is this quantity raised to a real power, and a nonnegative base has a nonnegative real power. Hence the norm is nonnegative.

**Key facts.** `FABL.gowersDiagonalInner_nonneg`.
