<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.continuous_lpMean_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of affine power means

**Claim.** For $s>0$, the uniform power mean of $x\mapsto 1+a\sigma(x_0)$ on the one-dimensional Boolean cube varies continuously with $a$.

**Proof.** Since $s>0$, the power mean is given by its positive-exponent formula, namely the $1/s$ power of the uniform expectation of the $s$th powers of the absolute values. The expectation is a finite sum over the two cube points. At each point, the function inside the absolute value is affine in $a$, hence continuous; taking absolute values and then the $s$th power preserves continuity. The finite weighted sum is therefore continuous and nonnegative. Taking its $1/s$ power is continuous on the nonnegative reals, so the power mean is continuous.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`.
