<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.selectedWidth_tail_probability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected Width Tail Bound

**Claim.** For a DNF formula $\varphi$ and a positive integer $k$, the uniform probability that its selected term has width at least $k$ is at most $|\varphi|/2^k$.

**Proof.** For each input, count the terms of $\varphi$ that both evaluate to $-1$ and have width at least $k$. If the selected width is at least $k$, the formula evaluates to $-1$; its selected term is then a term of the formula, evaluates to $-1$, and has width at least $k$. Thus the count is at least one. If the selected width is less than $k$, the indicator of that event is zero and is bounded by the nonnegative count. Taking expectations therefore bounds the probability of the selected-width event by the expected count.

Write the count as a sum of indicators, one for each term. Expectation distributes over this finite sum. For a term of width at least $k$, the probability that it evaluates to $-1$ is $2^{-\operatorname{width}(T)}$ (`uniformProbability_DNFTerm_eval_neg_one`), which is at most $2^{-k}$. A term of width below $k$ contributes zero to the indicator. Summing the resulting bound $2^{-k}$ over all terms gives $|\varphi|/2^k$. The facts that a true formula has a selected term in the formula (`selectedTerm_mem`) and that this term evaluates to $-1$ (`selectedTerm_eval`) justify the key pointwise bound; when the formula evaluates otherwise, the selected width is zero (`selectedWidth_eq_zero_of_eval_ne`).

**Key facts.** `FABL.DNFFormula.selectedWidth_eq_zero_of_eval_ne`, `FABL.DNFFormula.selectedTerm_mem`, `FABL.DNFFormula.selectedTerm_eval`, `FABL.uniformProbability_DNFTerm_eval_neg_one`, `FABL.expect_sum_list_map`.

**Caveat.** The supplied informal statement discusses random restrictions and a $(3/4)^w$ bound, but the formal statement and proof establish the selected-width bound $|\varphi|/2^k$ instead.
