<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.DNFFormula.uniformProbability_eval_neg_one_le_term_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Probability Bound for DNF Evaluation

**Claim.** Under the uniform distribution on the sign cube, the probability that a DNF formula evaluates to $-1$ is at most the sum over its terms of $2^{-\operatorname{width}(T)}$.

**Proof.** For each input, if the formula evaluates to $-1$, then some term evaluates to $-1$ (`FABL.DNFFormula.eval_eq_neg_one_iff`). Thus the indicator of the event that the formula evaluates to $-1$ is at most the sum of the indicators of the events that individual terms evaluate to $-1$: when the formula is true at least one summand is $1$, and otherwise the left side is zero while every summand is nonnegative. Taking expectations preserves this inequality. The expectation of the sum of the term indicators equals the sum of their expectations (`FABL.expect_sum_list_map`). Each term’s probability of evaluating to $-1$ is $2^{-\operatorname{width}(T)}$ (`FABL.uniformProbability_DNFTerm_eval_neg_one`), giving the claimed bound.

**Key facts.** `FABL.DNFFormula.eval_eq_neg_one_iff`, `FABL.expect_sum_list_map`, `FABL.uniformProbability_DNFTerm_eval_neg_one`.
