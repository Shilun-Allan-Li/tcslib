<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.propagationAssignment_one_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimal Propagation Has Value One

**Claim.** If the optimum value of the associated constraint satisfaction instance is $1$, then the assignment obtained by propagating the selected component labels has value $1$.

**Proof.** An optimum value of $1$ implies that the game is satisfiable (`satisfiable_iff_csp_satisfiable`). The propagated assignment then satisfies every game constraint (`propagationAssignment_fullySatisfied`). The correspondence between satisfaction in the game and satisfaction in its associated constraint satisfaction instance gives satisfaction there (`fullySatisfied_iff_csp`). Finally, a constraint satisfaction instance has value $1$ exactly when its assignment satisfies every constraint (`value_eq_one_iff_fullySatisfied`), so the propagated assignment has value $1$.

**Key facts.** `FABL.FiniteUniqueGame.satisfiable_iff_csp_satisfiable`, `FABL.FiniteUniqueGame.propagationAssignment_fullySatisfied`, `FABL.FiniteUniqueGame.fullySatisfied_iff_csp`, `FABL.CSPInstance.value_eq_one_iff_fullySatisfied`.
