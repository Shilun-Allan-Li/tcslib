<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.nat_succ_le_two_pow_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor bounded by a power of two

**Claim.** For every natural number $\ell$, one has $\ell+1\le 2^{\ell+1}$.

**Proof.** Proceed by induction on $\ell$. When $\ell=0$, the assertion is $1\le2$. For the step, assume $\ell+1\le2^{\ell+1}$. The next power is $2^{\ell+2}=2^{\ell+1}\cdot2$, which is at least $2(\ell+1)$. For $\ell\ge0$, $2(\ell+1)\ge \ell+2$, so $\ell+2\le2^{\ell+2}$, as required.
