<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.edgeError_optimalLabel_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimal labeling has bounded error

**Claim.** If the optimum value of the associated finite unique-game instance is at least $1-\delta$, then the expected fraction of violated constraints under an optimal labeling is at most $\delta$.

**Proof.** The edge error of the optimal labeling is nonnegative (`FABL.RegularUniqueGame.edgeError_nonneg`). By the identity between edge error and one minus the instance value (`FABL.RegularUniqueGame.edgeError_eq_one_sub_value`), this says that one minus the value attained by the optimal labeling is nonnegative. The value attained there is the optimum, so the error is exactly one minus the optimum. The assumed lower bound on the optimum therefore implies that this error is at most $\delta$.

**Key facts.** `FABL.RegularUniqueGame.edgeError_nonneg`, `FABL.RegularUniqueGame.edgeError_eq_one_sub_value`.
