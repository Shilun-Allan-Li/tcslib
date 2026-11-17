<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.satisfiable_iff_exists_component_labels -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiability via Component Labels

**Claim.** The game has a labeling satisfying every constraint if and only if some choice of one label for each connected component yields a satisfying labeling when propagated along the chosen paths.

**Proof.** Suppose first that a labeling satisfies every constraint. Choose at each component its root's label in this labeling. Propagation from these root labels recovers the original labeling (`propagatedLabel_eq_of_fullySatisfied`), so the propagated labeling satisfies every constraint. Conversely, if some choice of component root labels gives a propagated labeling satisfying every constraint, that propagated labeling itself is a satisfying labeling of the game. This proves both directions.

**Key facts.** `FABL.FiniteUniqueGame.propagatedLabel_eq_of_fullySatisfied`.
