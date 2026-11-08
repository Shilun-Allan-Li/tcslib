<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.sum_deltaRandomSubsetWeight_mul_sq_card_inter_sub_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted intersection-size variance

**Claim.** For every $U$, the weighted sum of $(|U\cap J|-\delta|U|)^2$ is $\delta(1-\delta)|U|$.

**Proof.** Write $X_J=|U\cap J|$ and $\mu=\delta|U|$. Expand each weighted square as $w_\delta(J)X_J^2-2\mu w_\delta(J)X_J+\mu^2w_\delta(J)$. Summing this identity over $J$, apply the second-moment identity (`FABL.sum_deltaRandomSubsetWeight_mul_sq_card_inter`), the first-moment identity (`FABL.sum_deltaRandomSubsetWeight_mul_card_inter`), and the total-weight identity (`FABL.sum_deltaRandomSubsetWeight`). The result is $\delta^2|U|^2+\delta(1-\delta)|U|-2\delta^2|U|^2+\delta^2|U|^2$, which simplifies to $\delta(1-\delta)|U|$.

**Key facts.** `FABL.sum_deltaRandomSubsetWeight_mul_sq_card_inter`, `FABL.sum_deltaRandomSubsetWeight_mul_card_inter`, `FABL.sum_deltaRandomSubsetWeight`.
