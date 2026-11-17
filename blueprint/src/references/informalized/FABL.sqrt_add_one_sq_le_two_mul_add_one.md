<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.sqrt_add_one_sq_le_two_mul_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural Square Root Bound

**Claim.** For every natural number $L$, $(\lfloor\sqrt L\rfloor+1)^2\le2(L+1)$, where the integer square root is $\operatorname{Nat.sqrt} L$.

**Proof.** Let $q=\operatorname{Nat.sqrt}L$. The integer square root satisfies $q^2\le L$. Also, nonnegativity of $(q-1)^2$ gives $2q\le q^2+1$. Expanding $(q+1)^2=q^2+2q+1$ and using these two bounds gives $(q+1)^2\le2q^2+2\le2L+2=2(L+1)$.
