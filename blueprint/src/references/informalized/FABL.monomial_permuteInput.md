<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.monomial_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial under Coordinate Permutation

**Claim.** Permuting the input coordinates by $\pi$ turns the monomial indexed by $S$ into the monomial indexed by the image $\pi(S)$ at the original input.

**Proof.** After expanding the definitions, the factor associated to each $i\in S$ is the sign value of $x_{\pi(i)}$. Reindex this finite product along the permutation $\pi$. Because a permutation is injective, distinct indices in $S$ give distinct indices in its image, and the reindexed factors are exactly those indexed by $\pi(S)$.
