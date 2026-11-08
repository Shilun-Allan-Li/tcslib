<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.propagationAssignment_fullySatisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction by Propagated Labels

**Claim.** If the game is satisfiable, then the assignment obtained by propagating the selected component labels satisfies every constraint.

**Proof.** Satisfiability yields a choice of root labels whose propagated labeling satisfies every constraint (`satisfiable_iff_exists_component_labels`). Consequently, for each component there exists a valid root label: the characterization of when a propagated labeling satisfies every constraint gives this validity (`fullySatisfied_propagatedLabel_iff`). The selected label for each component is therefore valid by `optimalComponentLabels_valid`. Applying that characterization again, now to the selected labels, shows that their propagated assignment satisfies every constraint.

**Key facts.** `FABL.FiniteUniqueGame.satisfiable_iff_exists_component_labels`, `FABL.FiniteUniqueGame.fullySatisfied_propagatedLabel_iff`, `FABL.FiniteUniqueGame.optimalComponentLabels_valid`.
