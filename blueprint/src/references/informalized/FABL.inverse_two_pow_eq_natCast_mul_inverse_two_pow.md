<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.inverse_two_pow_eq_natCast_mul_inverse_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal Power Identity

**Claim.** If $\ell\leq k$ are nonnegative integers, then $2^{-\ell}=2^{k-\ell}2^{-k}$.

**Proof.** The inequality gives $k=\ell+(k-\ell)$. Thus $2^k=2^\ell 2^{k-\ell}$. Taking reciprocals and rearranging yields $2^{-\ell}=2^{k-\ell}2^{-k}$. The natural-number coefficient in the statement is exactly the real power $2^{k-\ell}$.
