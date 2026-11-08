<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.exPrefix_of_satisfying -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth of an Existential Prefix

**Claim.** If a satisfying assignment agrees with the given assignment below index $i$, and the formula’s variable count is at most $i+j$, then the prefix of $j$ existential quantifiers starting at $i$ is true under the given assignment.

**Proof.** Induct on the number $j$ of existential quantifiers, allowing the assignment and starting index to vary. When $j=0$, the variable-count bound says every variable relevant to the CNF has index below $i$. The given assignment therefore agrees with the satisfying assignment on every relevant variable. Evaluation is invariant under assignments agreeing below the CNF’s variable count (`Complexity.eval_congr_of_lt_numVars`), so the CNF is true under the given assignment. For the successor case, choose the value at index $i$ to be its value in the satisfying assignment. Updating the given assignment at that index makes it agree with the satisfying assignment at every index below $i+1` (`Complexity.QBF.update_prefix_agreement`). The variable-count bound for the remaining $j$ quantifiers follows by arithmetic, so the induction hypothesis proves the remaining existential prefix.

**Key facts.** `Complexity.eval_congr_of_lt_numVars`, `Complexity.QBF.update_prefix_agreement`.
