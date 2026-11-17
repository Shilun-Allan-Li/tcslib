<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.fullySatisfied_iff_csp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalence of Full Satisfaction Formulations

**Claim.** A labeling satisfies every game constraint if and only if it satisfies every constraint in the associated constraint satisfaction instance.

**Proof.** Suppose first that every game constraint is satisfied. Any constraint occurrence in the associated instance is the image of some game edge under the construction of that instance. The satisfaction criterion (`FABL.FiniteUniqueGame.constraint_satisfied_iff`) turns the game’s satisfaction equation for that edge into satisfaction of its associated CSP constraint. Conversely, each game edge contributes its associated CSP constraint to the instance. If every instance constraint is satisfied, this constraint is satisfied in particular; the same criterion then gives the game’s satisfaction equation for the edge. Since the edge was arbitrary, all game constraints are satisfied.

**Key facts.** `FABL.FiniteUniqueGame.constraint_satisfied_iff`.
