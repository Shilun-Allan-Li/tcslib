<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.inversePathSize_le_inverseTwoPow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inverse Path Size Bound

**Claim.** If a path has length at least $k$, then $2^{-	ext{length}(P)}\leq 2^{-k}$.

**Proof.** By definition, the inverse path size is the reciprocal of $2^{\mathrm{length}(P)}$. Since $2>1$ and $k\leq\mathrm{length}(P)$, monotonicity of natural powers gives $2^k\leq 2^{\mathrm{length}(P)}$. Both powers are positive, so taking reciprocals reverses the inequality and yields the claim.
