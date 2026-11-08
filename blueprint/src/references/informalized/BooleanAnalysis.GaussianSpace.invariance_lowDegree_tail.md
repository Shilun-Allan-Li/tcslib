<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceExtensions.lean :: BooleanAnalysis.GaussianSpace.invariance_lowDegree_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree and Tail Invariance Bound

**Claim.** For a function of variance at most one, the discrepancy between its uniform-cube Lipschitz expectation and the corresponding Gaussian polynomial integral is bounded by a constant times the Lipschitz constant and the sum of the low-degree approximation error and the high-degree tail norm, as stated.

**Proof.** Choose the positive constant $K+2$, where $K$ is supplied by the low-degree Boolean-to-Gaussian invariance estimate (`invariance_lipschitz_boolean_gaussian`). Let $d=\lfloor k\rfloor$, let $g$ be the degree-$d$ Fourier truncation of $f$, and let $T$ be the norm of the remaining high-degree part. The decomposition identity `low_plus_high_eq` says pointwise that $f-g$ is exactly this high-degree part. The Lipschitz expectation estimate (`lipschitz_expect_sub_le_l2Norm`) therefore bounds the change from $f$ to $g$ on the cube by $cT$. The truncation has degree at most $d$ (`lowDegreePart_polynomial_degree`) and variance at most that of $f$ (`lowDegreePart_variance_le`), so the Boolean-to-Gaussian estimate applies to $g$. It bounds the discrepancy for $g$ by $Kc2^d\varepsilon^{1/4}$; since $d\le k$, this is at most $Kc2^k\varepsilon^{1/4}$. Finally, the Gaussian-extension Lipschitz estimate (`lipschitz_gaussian_extension_sub_le_l2Norm`) bounds the change from $g$ back to $f$ on the Gaussian side by $cT$. The triangle inequality adds these three contributions. Since $K>0$, their sum is at most $(K+2)c(2^k\varepsilon^{1/4}+T)$, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.invariance_lipschitz_boolean_gaussian`, `BooleanAnalysis.GaussianSpace.Invariance.lowDegreePart_polynomial_degree`, `BooleanAnalysis.GaussianSpace.Invariance.lowDegreePart_variance_le`, `KKL.low_plus_high_eq`, `BooleanAnalysis.GaussianSpace.Invariance.lipschitz_expect_sub_le_l2Norm`, `BooleanAnalysis.GaussianSpace.Invariance.lipschitz_gaussian_extension_sub_le_l2Norm`.
