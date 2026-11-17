<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.HasSmallStableInfluences.isLowDegreeFourierRegular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Fourier Regularity

**Claim.** If every coordinate has stable influence at parameter $1-\delta$ at most $\epsilon$, where $0\le\delta<1$, then every nonempty set $S$ with $|S|\le k$ satisfies $|\widehat f(S)|\le\sqrt{\epsilon/(1-\delta)^{k-1}}$.

**Proof.** Fix such a set $S$ and choose $i\in S$. Put $\rho=1-\delta$, so $0<\rho\le1$. Since $|S|\le k$ and $S$ is nonempty, $|S|-1\le k-1$. For a base in $(0,1]$, increasing the exponent can only decrease its power, so $\rho^{k-1}\le\rho^{|S|-1}$. Multiplying by the nonnegative square of the Fourier coefficient preserves this inequality. The resulting weighted square is one term in the stable influence at coordinate $i$, and hence is at most that stable influence (`rho_pow_card_sub_one_mul_sq_fourierCoeff_le_stableInfluence`), which is at most $\epsilon$ by hypothesis. Finally, divide by the positive quantity $\rho^{k-1}$ and take square roots to obtain the claimed bound.

**Key facts.** `FABL.rho_pow_card_sub_one_mul_sq_fourierCoeff_le_stableInfluence`.
