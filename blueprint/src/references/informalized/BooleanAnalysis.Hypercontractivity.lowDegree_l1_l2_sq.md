<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.lowDegree_l1_l2_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree $L^1$–$L^2$ Bound

**Claim.** If $f$ has Fourier degree at most $k$, then $e^{-2k}\langle f,f\rangle\leq(\mathbb E|f|)^2$.

**Proof.** Form the multilinear polynomial whose coefficient at each set $S$ is the Fourier coefficient of $f$. The degree assumption on $f$ says precisely that coefficients indexed by sets larger than $k$ vanish, so this polynomial has degree at most $k$. The Walsh expansion identifies its evaluation on the cube with $f$. Apply the low-degree polynomial inequality to obtain $e^{-2k}\sum_S\widehat f(S)^2\leq(\mathbb E|f|)^2$. Parseval identifies the sum of squared Fourier coefficients with $\langle f,f\rangle$, giving the claim.

**Key facts.** `BooleanAnalysis.walsh_expansion`, `BooleanAnalysis.ThresholdFunctions.low_degree_l1_l2_sq`, `BooleanAnalysis.parseval`.
