<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.lpMean_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in Function Values

**Claim.** If $p>0$, $f$ is nonnegative, and $f(x)\le g(x)$ at every point, then $M_p(f)\le M_p(g)$.

**Proof.** The pointwise assumptions imply $g(x)\ge0$ as well. By the positive-exponent formula (`lpMean_of_pos`), it suffices to compare the expectations of $|f|^p$ and $|g|^p$, and nonnegativity lets us remove the absolute values. The function $t\mapsto t^p$ is increasing on $[0,\infty)$ for $p>0$, so $f(x)^p\le g(x)^p$ at every point. Summing these inequalities with the nonnegative uniform weights gives $\mathbb E f^p\le\mathbb E g^p$. The outer power $1/p$ is increasing on nonnegative reals, proving the result. The expectation-as-finite-average identity (`expect_eq_fintypeExpect`) expresses the expectation as this weighted sum.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.expect_eq_fintypeExpect`.
