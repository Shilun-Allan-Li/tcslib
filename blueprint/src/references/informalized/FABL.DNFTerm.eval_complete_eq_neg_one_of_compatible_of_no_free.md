<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.eval_complete_eq_neg_one_of_compatible_of_no_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under a compatible restriction

**Claim.** If some completion of a coordinate restriction makes every literal of a term match its required sign, and no literal lies at a free coordinate, then every completion makes every literal match its required sign.

**Proof.** Choose a completion that satisfies the term, using compatibility. By the characterization of term evaluation (FABL.DNFTerm.eval_eq_neg_one_iff), each literal in the term has the required sign at its coordinate under this chosen completion. Now take any literal and let $j$ be its position in the list. Since the set of free literal positions is empty, this position is not free, so its coordinate is fixed either to $1$ or to $-1$. Both completions therefore assign the same sign at that coordinate. The chosen completion satisfies the literal, hence so does the arbitrary completion. This holds for every literal, and the same characterization shows that the term evaluates to $-1$ under the arbitrary completion.

**Key facts.** `FABL.DNFTerm.eval_eq_neg_one_iff`.
