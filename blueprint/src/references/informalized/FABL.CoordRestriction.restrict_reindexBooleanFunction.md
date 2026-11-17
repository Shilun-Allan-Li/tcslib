<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.restrict_reindexBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Under Reindexing

**Claim.** Restricting the reindexed function according to $\rho$ is the function obtained by restricting $f$ using the states transported along the coordinate bijection and then evaluating at the correspondingly reindexed input.

**Proof.** Unfold the definitions at an arbitrary binary input. The left side evaluates the reindexed function at the completion determined by $\rho$; by the definition of reindexing, this evaluates $f$ at the input whose coordinate $i$ is the completed value at $e(i)$. Completing with $\rho$ at coordinate $e(i)$ gives exactly the same value as completing the reindexed restriction with state $\rho(e(i))$ at coordinate $i$ and input value $x(e(i))$. Thus the two expressions are definitionally the same at every input.
