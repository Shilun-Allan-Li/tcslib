<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.maxCutSatisfyingAssignment_fullySatisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiable Cut Instances Are Fully Satisfied

**Claim.** If the optimum value of a maximum-cut instance is $1$, then its optimal assignment satisfies every constraint.

**Proof.** The optimum is the value of the instance at its optimal assignment. The hypothesis that the optimum is $1$ therefore says that this assignment has value $1$. The value-one characterization states that an assignment has value $1$ exactly when it fully satisfies the instance (`CSPInstance.value_eq_one_iff_fullySatisfied`). Applying its forward implication yields that the optimal assignment satisfies every constraint.

**Key facts.** `FABL.CSPInstance.value_eq_one_iff_fullySatisfied`.
