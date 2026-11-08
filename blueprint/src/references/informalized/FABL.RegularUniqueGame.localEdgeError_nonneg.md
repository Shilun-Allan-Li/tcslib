<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.localEdgeError_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Local Edge Error

**Claim.** For any labeling and fixed vertex, the average over its neighbors of the indicator that the edge constraint fails is nonnegative.

**Proof.** For each neighbor, the edge failure indicator is either $0$, when the constraint is satisfied, or $1$, when it fails. It is therefore nonnegative pointwise. The average of nonnegative real numbers over the finite neighbor set is nonnegative, which proves the claim.
