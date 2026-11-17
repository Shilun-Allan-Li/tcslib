<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/LaplacianAndPoincare.lean :: FABL.totalInfluence_eq_sum_card_mul_sq_fourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier formula for total influence

**Claim.** For every real-valued function on the sign cube, its total influence is the sum over subsets $S$ of $|S|\widehat f(S)^2$.

**Proof.** For each coordinate $i$, its influence is the sum of $\widehat f(S)^2$ over subsets containing $i$ (FABL.influence_eq_sum_sq_fourierCoeff). Sum this identity over all coordinates and interchange the two finite sums. For a fixed subset $S$, its squared Fourier coefficient then appears once for each coordinate in $S$, hence exactly $|S|$ times. This gives $I[f]=\sum_S |S|\widehat f(S)^2$.

**Key facts.** `FABL.influence_eq_sum_sq_fourierCoeff`.
