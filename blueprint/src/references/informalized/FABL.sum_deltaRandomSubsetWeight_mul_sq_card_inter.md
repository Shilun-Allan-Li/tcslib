<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.sum_deltaRandomSubsetWeight_mul_sq_card_inter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment of intersection size

**Claim.** The weighted sum of $|U\cap J|^2$ equals $\delta^2|U|^2+\delta(1-\delta)|U|$.

**Proof.** Write the square of the intersection size as a sum over ordered pairs $i,j\in U$ of the indicator that both coordinates lie in $J$ (`FABL.sq_card_inter_eq_sum_pairIndicator`). Interchange the finite sums so that, for each pair, one sums its indicator against the subset weights. The total is $\delta$ when $i=j$ and $\delta^2$ when $i\ne j$ (`FABL.sum_deltaRandomSubsetWeight_pair_mem`). Summing these contributions over pairs gives $\delta^2|U|^2+\delta(1-\delta)|U|$: the $|U|$ diagonal pairs contribute $\delta$, while the off-diagonal pairs contribute $\delta^2$, equivalently the total is $\delta^2|U|^2+(\delta-\delta^2)|U|$ (`FABL.sum_pairDiagonalWeight`).

**Key facts.** `FABL.sq_card_inter_eq_sum_pairIndicator`, `FABL.sum_deltaRandomSubsetWeight_pair_mem`, `FABL.sum_pairDiagonalWeight`.
