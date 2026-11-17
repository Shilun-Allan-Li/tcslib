<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.lpMean_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Homogeneity of Power Means

**Claim.** For $p,c>0$ and $f:\{0,1\}^n\to\mathbb R$, the extended power mean of $cf$ with exponent $p$ is $c$ times the extended power mean of $f$.

**Proof.** Because $p>0$, the positive-exponent formula identifies each extended power mean with the corresponding moment raised to $1/p$ (`lpMean_of_pos`). Pointwise, $|cf(x)|^p=c^p|f(x)|^p$, using $c>0$ to take the real power of the product. Linearity of the finite uniform expectation then gives $\mathbb E|cf|^p=c^p\mathbb E|f|^p$. The moment of $|f|^p$ is nonnegative (`expect_rpow_abs_nonneg`), so real powers distribute over the product of the nonnegative factors. Finally, $(c^p)^{1/p}=c$, since $c>0$ and $p(1/p)=1$. Combining these identities proves the claimed homogeneity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg`.
