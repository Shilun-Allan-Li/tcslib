<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/AffineKhintchine.lean :: BooleanAnalysis.ThresholdFunctions.weightLevel1_antipode_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-level weight bound

**Claim.** If the antipodal differences of $g$ satisfy $|g(x)-g(\bar x)|\le 2|a|$ for every $x$, then the Fourier weight of $g$ at level $1$ is at most $a^2$.

**Proof.** Define the odd part $u(x)=(g(x)-g(\bar x))/2$. For every set $S$ of size one, the Fourier coefficient of $u$ at $S$ equals that of $g$. Indeed, the coefficient of the antipodally composed function $x\mapsto g(\bar x)$ at $S$ is $-\widehat g(S)$, by the Fourier coefficient transformation rule under flipping every coordinate (`fourierCoeff_comp_flipSet` together with `flipSet_univ`). Expanding the definition of $u$ inside its coefficient and using linearity of expectation (`expect_add`, `expect_const_mul`) gives $\widehat u(S)=\widehat g(S)$.\n\nParseval's identity expresses $\langle u,u\rangle$ as the sum of squares of all Fourier coefficients of $u$ (`parseval`). The level-one terms in this sum equal those for $g$, and every remaining term is nonnegative. Hence the level-one weight of $g$ is at most $\langle u,u\rangle$. The assumed bound gives $|u(x)|\le |a|$ pointwise, so $u(x)^2\le a^2$. Monotonicity of expectation (`expect_mono`) bounds $\langle u,u\rangle=\mathbb E[u^2]$ by the expectation of the constant $a^2$, which equals $a^2$ (`expect_const`).

**Key facts.** `BooleanAnalysis.ThresholdFunctions.fourierCoeff_comp_flipSet`, `BooleanAnalysis.ThresholdFunctions.flipSet_univ`, `BooleanAnalysis.ThresholdFunctions.expect_add`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.parseval`, `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.ThresholdFunctions.expect_const`.
