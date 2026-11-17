<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/AffineKhintchine.lean :: BooleanAnalysis.ThresholdFunctions.spectral_inequality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance and influence inequality

**Claim.** For a real-valued function $g$ on the Boolean cube, twice its variance is at most its total influence plus its Fourier weight at level one.

**Proof.** Parseval's identity (BooleanAnalysis.parseval) writes $\mathbb E[g^2]$ as the sum of the squared Fourier coefficients, and the degree formula for total influence (BooleanAnalysis.totalInfluence_eq_sum_sq_deg) writes the total influence as the sum of those squares weighted by $|S|$. The empty-set coefficient is $\mathbb E g$ (BooleanAnalysis.fourierCoeff_empty), so subtracting $(\mathbb E g)^2$ removes the empty-set contribution from Parseval. After multiplying by $2$, the desired inequality reduces term by term to comparing $2\widehat g(S)^2$ with $|S|\widehat g(S)^2$ plus the level-one contribution. For $|S|=0$, both sides contribute zero after the mean is removed. For $|S|=1$, the level-one weight supplies one additional copy of the square, so the two sides agree. For $|S|\ge2$, the influence term alone has coefficient at least $2$, and the level-one contribution is zero. Summing these comparisons proves the inequality.

**Key facts.** `BooleanAnalysis.fourierCoeff_empty`, `BooleanAnalysis.parseval`, `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`.
