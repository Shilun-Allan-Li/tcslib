<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.zmodProductFourierBasis_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Fourier basis vectors

**Claim.** For every positive modulus, natural number $n$, and index function $\alpha$, the Fourier basis vector indexed by $\alpha$ is the product character indexed by $\alpha$.

**Proof.** The product Fourier basis is the character basis reindexed by the inverse of the additive equivalence from index functions to product characters. A character basis vector at a character is that character itself (`FABL.abelianFourierBasis_apply`). Applying this to the reindexed index $\alpha$ gives the product character indexed by $\alpha$.

**Key facts.** `FABL.abelianFourierBasis_apply`.
