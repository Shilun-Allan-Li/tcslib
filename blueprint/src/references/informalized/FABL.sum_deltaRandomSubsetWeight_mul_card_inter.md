<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.sum_deltaRandomSubsetWeight_mul_card_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected intersection size

**Claim.** The weighted sum of $|U\cap J|$ over all subsets $J$ equals $\delta|U|$.

**Proof.** Express $|U\cap J|$ as a sum over coordinates $i\in U$ of the indicator that $i\in J$ (`FABL.card_inter_eq_sum_memIndicator`). Multiplying by the weight and summing over $J$, interchange the two finite sums. For each fixed $i\in U$, the indicator restricts the inner sum to subsets containing $i$; its total weight is $\delta$ (`FABL.sum_deltaRandomSubsetWeight_mem`). Thus each of the $|U|$ coordinates contributes $\delta$, giving $\delta|U|$.

**Key facts.** `FABL.card_inter_eq_sum_memIndicator`, `FABL.sum_deltaRandomSubsetWeight_mem`.
