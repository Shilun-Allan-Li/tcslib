<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.satisfiable_iff_exists_fullySatisfied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiability and Full Satisfaction

**Claim.** The instance is satisfiable, meaning its optimum value is $1$, if and only if there is an assignment satisfying every constraint.

**Proof.** Suppose first that the optimum is $1$. The optimal assignment therefore has value $1$, and the characterization of assignments of value $1` by full satisfaction (`value_eq_one_iff_fullySatisfied`) shows that it satisfies every constraint.

Conversely, suppose an assignment satisfies every constraint. The same characterization gives that its value is $1$. The optimum is at least the value of any assignment (`value_le_optimum`), hence is at least $1$; it is also at most $1$ (`optimum_le_one`). Thus the optimum equals $1, as required.

**Key facts.** `FABL.CSPInstance.value_eq_one_iff_fullySatisfied`, `FABL.CSPInstance.optimum_le_one`, `FABL.CSPInstance.value_le_optimum`.
