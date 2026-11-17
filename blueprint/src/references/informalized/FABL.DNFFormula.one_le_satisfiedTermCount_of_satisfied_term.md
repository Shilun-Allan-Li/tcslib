<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.DNFFormula.one_le_satisfiedTermCount_of_satisfied_term -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Satisfied-Term Count

**Claim.** If a term of a DNF formula is satisfied by an input, then the number of terms satisfied by that input is at least $1$.

**Proof.** Because $T$ occurs in the list of terms, it has some position $i$ in that list. At this position the term is exactly $T$, so its indicator is $1$: a term’s true indicator equals $1$ precisely when the term evaluates to $-1$ (`FABL.DNFTerm.trueIndicator_eq_one_iff`). The satisfied-term count is the sum of these indicators over all positions. Every summand is nonnegative (`FABL.DNFTerm.trueIndicator_nonneg`), so this sum is at least its summand at position $i$, namely $1$.

**Key facts.** `FABL.DNFTerm.trueIndicator_eq_one_iff`, `FABL.DNFTerm.trueIndicator_nonneg`.
