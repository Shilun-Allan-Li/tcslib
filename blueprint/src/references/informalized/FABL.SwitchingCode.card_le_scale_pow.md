<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingCode.card_le_scale_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching-Code Cardinality Bound

**Claim.** For all nonnegative integers $w$ and $k$, the number of switching codes of width $w$ and index $k$ is at most $(9w/4)^k$.

**Proof.** Proceed by strong induction on the index. At index zero there are no switching codes, so the bound holds. For index $m+1$, the cardinality recurrence (`card_succ`) splits the count into final-block codes and codes formed from a full block followed by a shorter switching code. The final-block contribution is at most $(9w/4)^{m+1}$ times its coefficient and remainder, by the bound for the final-block term (`choose_final_le`). For each summand indexed by $i<m$, the full-block factor is bounded using the full-block estimate (`choose_full_le`), and the tail count is bounded by the induction hypothesis at index $m-i$. Since $(9w/4)^{i+1}(9w/4)^{m-i}=(9w/4)^{m+1}$, summing these estimates bounds the full-block contributions by this common power times the sum of the corresponding coefficients. The recurrence’s coefficients combine with the final remainder to a quantity at most $1$: the sum of full coefficients is bounded by `sum_fullCoefficient_range`, and the remainder is bounded by `finalRemainder_le` (with the smallest case checked directly). Factoring out $(9w/4)^{m+1}$ therefore gives the desired bound.

**Key facts.** `FABL.SwitchingCode.card_succ`, `FABL.SwitchingCode.choose_final_le`, `FABL.SwitchingCode.choose_full_le`, `FABL.SwitchingCode.sum_fullCoefficient_range`, `FABL.SwitchingCode.finalRemainder_le`.
