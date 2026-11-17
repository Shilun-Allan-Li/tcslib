<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.DNFFormula.satisfiedTermCount_eq_zero_of_no_satisfied_term -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Count Without Satisfied Terms

**Claim.** If no term of a DNF formula evaluates to $-1$ at an input, then the number of terms evaluating to $-1$ there is zero.

**Proof.** Write the satisfied-term count as a sum over the positions in the term list. At any position, the term there belongs to the list, so the hypothesis that no listed term evaluates to $-1$ implies that this term does not evaluate to $-1$. Its true indicator is therefore $0`, by the definition of the indicator. Every summand is zero, and hence their sum is zero.
