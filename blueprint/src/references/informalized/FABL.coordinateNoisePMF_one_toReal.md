<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.coordinateNoisePMF_one_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise from the positive sign

**Claim.** For $\rho\in[-1,1]$ and a sign $y$, noise started at $1$ assigns probability $(1+\rho)/2$ to $y=1$ and $(1-\rho)/2$ otherwise.

**Proof.** There are two cases. If $y=1$, the output is the starting sign, so the probability is the keep probability $p=(1+\rho)/2$ (`coordinateNoisePMF_apply_self_middleLayer`). If $y=-1$, the output is the negative of the starting sign, so its probability is $1-p$ (`coordinateNoisePMF_apply_neg_middleLayer`). Since $p\leq1$ (`correlationKeepProbability_le_one`), converting this complementary probability from extended nonnegative reals to reals is valid; substituting $p=(1+\rho)/2$ and simplifying gives $(1-\rho)/2$.

**Key facts.** `FABL.coordinateNoisePMF_apply_self_middleLayer`, `FABL.coordinateNoisePMF_apply_neg_middleLayer`, `FABL.correlationKeepProbability_le_one`.
