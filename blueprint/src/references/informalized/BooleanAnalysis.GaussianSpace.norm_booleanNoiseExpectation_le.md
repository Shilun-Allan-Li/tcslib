<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/UniformTransfer.lean :: BooleanAnalysis.GaussianSpace.norm_booleanNoiseExpectation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean noise averaging norm bound

**Claim.** If $0\leq\rho\leq1$ and every value of a complex-valued function $F$ on pairs of Boolean inputs has norm at most $C$, then the norm of its noise-kernel weighted average is at most $C$.

**Proof.** The uniform weight is nonnegative. Taking the norm of the weighted sum and applying the triangle inequality twice, first to the sum over the first input and then to the sum over the second, bounds it by the uniform weight times the sum of the norms of the summands. The norm of each summand is the noise kernel times the norm of the corresponding value of $F$: the kernel is nonnegative under $0\leq\rho\leq1$ (`noiseKernel_nonneg`), and that value has norm at most $C$. Thus the resulting bound is the uniform weight times the sum of the kernels multiplied by $C$. For each fixed first input, the kernel sums to $1$ over the second input (`noiseKernel_sum_right`). Summing this identity over first inputs and multiplying by the uniform weight gives total mass $1$, so the bound reduces to $C$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.noiseKernel_nonneg`, `BooleanAnalysis.Hypercontractivity.noiseKernel_sum_right`.
