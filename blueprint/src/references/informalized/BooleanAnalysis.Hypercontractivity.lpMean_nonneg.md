<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.lpMean_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Positive Power Means

**Claim.** For $p>0$ and any $f:\{0,1\}^n\to\mathbb R$, the extended power mean $M_p(f)$ is nonnegative.

**Proof.** The positive-exponent formula (`lpMean_of_pos`) writes $M_p(f)$ as $(\mathbb E|f|^p)^{1/p}$. The expectation in the base is nonnegative, since each term $|f(x)|^p$ is nonnegative and the uniform weights are nonnegative (`expect_rpow_abs_nonneg`). A real power of a nonnegative base is nonnegative, so $M_p(f)\ge0$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg`.
