<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Basic.lean :: KKL.influence_noiseOp_le_noisyInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence under the noise operator

**Claim.** For $0\le\rho\le1$, the influence of coordinate $i$ on the noise-operator image of $f$ is at most $\sum_{S\ni i}\rho^{|S|-1}\widehat f(S)^2$.

**Proof.** Use the Fourier formula for influence, whose summand at $S$ is the squared Fourier coefficient when $i\in S$ and zero otherwise (BooleanAnalysis.influence_eq_sum_fourier). The noise operator multiplies the coefficient at $S$ by $\rho^{|S|}$ (BooleanAnalysis.noiseOp_fourier), so for $i\in S$ the new summand is $\rho^{2|S|}\widehat f(S)^2$. Since $i\in S$, we have $|S|\ge1$, hence $2|S|\ge |S|-1$. For $0\le\rho\le1$, powers decrease as the exponent increases, giving $\rho^{2|S|}\le\rho^{|S|-1}$. Multiplication by the nonnegative square $\widehat f(S)^2$ preserves this inequality. For $i\notin S$, both summands vanish. Summing over all $S$ yields the bound.

**Key facts.** `BooleanAnalysis.influence_eq_sum_fourier`, `BooleanAnalysis.noiseOp_fourier`.
