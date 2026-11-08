<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.positiveBias_eq_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Bias from the Mean

**Claim.** For every Boolean function $f$ on a finite sign cube, its positive bias is $(1+\mathbb{E}[f])/2$, where the output sign is interpreted as the real number $+1$ or $-1$.

**Proof.** Write $p_+$ and $p_-$ for the probabilities that $f$ equals $+1$ and $-1$. The mean of the real-valued output is $p_+-p_-$ (`mean_eq_probability_one_sub_probability_neg_one`), while the two probabilities sum to $1$ (`uniformProbability_one_add_neg_one_eq_one`). Thus $1+\mathbb{E}[f]=1+p_+-p_-=2p_+$, and the positive bias is $p_+$.

**Key facts.** `FABL.mean_eq_probability_one_sub_probability_neg_one`, `FABL.uniformProbability_one_add_neg_one_eq_one`.
