<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.lpMean_dim_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Mean on the Zero Dimensional Cube

**Claim.** If $p>0$ and $f:\{0,1\}^0\to\mathbb R$ is nonnegative, its extended power mean with exponent $p$ equals its value at the unique point of the zero dimensional cube.

**Proof.** By the positive-exponent formula (`lpMean_of_pos`), the mean is the $1/p$ power of the expectation of $|f|^p$. The zero dimensional cube has just one point, and its uniform weight is $1$, so this expectation is $|f(*)|^p$. Nonnegativity of $f(*)$ removes the absolute value. Thus the mean is $(f(*)^p)^{1/p}=f(*)$: the real-power product law applies to this nonnegative value, and $p(1/p)=1$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`.
