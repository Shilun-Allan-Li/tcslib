<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.DNFFormula.toBooleanFunction_eq_of_width_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constancy of Width-Zero Formulas

**Claim.** A DNF formula of width zero defines a Boolean function that takes the same value on every pair of inputs in the sign cube.

**Proof.** First consider the case where the formula has no terms. Its disjunction is false at every input, so its associated function is constantly $1$. Otherwise choose a term $T$ in the formula. Every term has width at most the formula’s width (`FABL.DNFFormula.width_le_of_mem`), so $T$ has width zero. Hence its literal list is empty. An empty term is satisfied at every input: the condition that all its literals are satisfied holds vacuously (`FABL.DNFTerm.eval_eq_neg_one_iff`). Therefore the formula has a satisfied term at both inputs, and the characterization of formula evaluation by existence of a satisfied term (`FABL.DNFFormula.eval_eq_neg_one_iff`) shows that it evaluates to $-1$ at each. In either case its values at the two inputs agree.

**Key facts.** `FABL.DNFFormula.width_le_of_mem`, `FABL.DNFTerm.eval_eq_neg_one_iff`, `FABL.DNFFormula.eval_eq_neg_one_iff`.
