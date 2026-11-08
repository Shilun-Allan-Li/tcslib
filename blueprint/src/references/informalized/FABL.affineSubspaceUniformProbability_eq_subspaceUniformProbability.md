<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.affineSubspaceUniformProbability_eq_subspaceUniformProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine and linear subspace probabilities

**Claim.** For a linear subspace $H$ and vector $a$, the probability that a uniform vector lies in $a+H$ equals the probability that it lies in $H$.

**Proof.** Express each probability as the average of the indicator of its corresponding set. The indicator of the affine translate at $x$ equals the indicator of $H$ at $x+a$ (`FABL.setIndicator_binaryAffineSubspace_eq_translate`). Translation by $a$ is a bijection of the ambient finite vector space, so changing variables in the uniform average leaves the expectation unchanged. The resulting average is the indicator average for $H$, which is its uniform probability.

**Key facts.** `FABL.setIndicator_binaryAffineSubspace_eq_translate`.
