<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.decisionTreeDepth_binaryBooleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Preserves Decision Tree Depth

**Claim.** The minimum depth of a binary decision tree computing the Boolean dual of a function equals the minimum depth of a binary decision tree computing the function.

**Proof.** The one-sided depth inequality says that dualizing a function cannot increase its minimum decision-tree depth (\texttt{decisionTreeDepth_binaryBooleanDual_le}). Apply that same inequality to the dual function. Since duality is an involution (\texttt{binaryBooleanDual_involutive}), the dual of the dual is the original function, giving the reverse inequality. The two inequalities imply equality.

**Key facts.** `FABL.decisionTreeDepth_binaryBooleanDual_le`, `FABL.binaryBooleanDual_involutive`.
