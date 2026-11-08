<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.satisfiable_iff_csp_satisfiable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalent Satisfiability Conditions

**Claim.** The game has a labeling satisfying every constraint if and only if its associated constraint satisfaction instance has optimum value $1$.

**Proof.** A game labeling satisfies every constraint exactly when it satisfies the associated constraint satisfaction instance (`fullySatisfied_iff_csp`). Also, the associated instance is satisfiable exactly when there exists an assignment satisfying every constraint (`CSPInstance.satisfiable_iff_exists_fullySatisfied`). Replacing each game labeling by the same assignment viewed in the associated instance, and using these equivalences, identifies the two existence statements and hence the two notions of satisfiability.

**Key facts.** `FABL.CSPInstance.satisfiable_iff_exists_fullySatisfied`, `FABL.FiniteUniqueGame.fullySatisfied_iff_csp`.
