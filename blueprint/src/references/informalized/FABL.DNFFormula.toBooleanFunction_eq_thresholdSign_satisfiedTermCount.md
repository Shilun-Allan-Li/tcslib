<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.DNFFormula.toBooleanFunction_eq_thresholdSign_satisfiedTermCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Representation of DNF Evaluation

**Claim.** For a DNF formula and an input, the formula’s value is the threshold sign of one half minus the number of terms satisfied by that input.

**Proof.** Split into whether some term evaluates to $-1$. If such a term exists, the DNF evaluates to $-1$ by the characterization of a negative DNF value (`FABL.DNFFormula.eval_eq_neg_one_iff`). The satisfied-term count is then at least $1$ (`FABL.DNFFormula.one_le_satisfiedTermCount_of_satisfied_term`), so one half minus that count is negative; its threshold sign is $-1$ (`FABL.thresholdSign_of_neg`). If no term is satisfied, the DNF cannot evaluate to $-1$, again by the characterization, and since its value is a sign it must therefore be $1$. In this case the satisfied-term count is zero (`FABL.DNFFormula.satisfiedTermCount_eq_zero_of_no_satisfied_term`), so the threshold argument is one half, which is nonnegative; its threshold sign is $1$ (`FABL.thresholdSign_of_nonneg`).

**Key facts.** `FABL.DNFFormula.eval_eq_neg_one_iff`, `FABL.DNFFormula.one_le_satisfiedTermCount_of_satisfied_term`, `FABL.thresholdSign_of_neg`, `FABL.DNFFormula.satisfiedTermCount_eq_zero_of_no_satisfied_term`, `FABL.thresholdSign_of_nonneg`.
