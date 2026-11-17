<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.two_mul_inv_two_pow_eq_inv_pred_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal powers of two

**Claim.** For every positive natural number $w$, $2\cdot(2^w)^{-1}=(2^{w-1})^{-1}$.

**Proof.** Since $w>0$, we have $w=(w-1)+1$. The successor law for powers therefore gives $2^w=2^{w-1}\cdot2=2\cdot2^{w-1}$. Taking reciprocals in the reals and simplifying the resulting nonzero factors yields the stated identity.
