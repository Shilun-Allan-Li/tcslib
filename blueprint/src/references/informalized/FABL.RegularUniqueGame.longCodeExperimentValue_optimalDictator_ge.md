<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.longCodeExperimentValue_optimalDictator_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimal dictator experiment guarantee

**Claim.** If the associated unique-game instance has optimum at least $1-\delta$, then the dictator code induced by an optimal labeling has experiment value at least $\beta-r\delta$.

**Proof.** The optimum hypothesis implies that the edge error of the optimal labeling is at most $\delta$ (\texttt{FABL.RegularUniqueGame.edgeError\_optimalLabel\_le}). Apply the low-edge-error dictator guarantee to this labeling, with the given arity bound and dictator completeness assumption (\texttt{FABL.RegularUniqueGame.longCodeExperimentValue\_dictator\_ge\_of\_edgeError}). Its conclusion is exactly the stated lower bound.

**Key facts.** `FABL.RegularUniqueGame.edgeError_optimalLabel_le`, `FABL.RegularUniqueGame.longCodeExperimentValue_dictator_ge_of_edgeError`.
