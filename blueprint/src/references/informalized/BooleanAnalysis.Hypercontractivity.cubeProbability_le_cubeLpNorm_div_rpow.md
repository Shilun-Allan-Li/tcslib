<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.cubeProbability_le_cubeLpNorm_div_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moment Tail Bound

**Claim.** For a function $f$ on the Boolean cube and positive $q,c$, the uniform probability that $|f(x)|\ge c$ is at most $(\|f\|_q/c)^q$.

**Proof.** At each point of the cube, if $|f(x)|\ge c$, monotonicity of the positive-power function gives $c^q\le |f(x)|^q$. If the threshold condition fails, its indicator is zero, while $|f(x)|^q$ remains nonnegative. Thus, pointwise, $c^q$ times the indicator of the threshold event is at most $|f(x)|^q$. Taking uniform expectations preserves this inequality. The expectation of a constant multiple factors as that constant times the expectation (\texttt{BooleanAnalysis.ThresholdFunctions.expect_const_mul}), and the expectation of the indicator is the event's probability. Hence $c^q\Pr(|f|\ge c)\le\mathbb E|f|^q$. By the definition of the $q$-norm, $\mathbb E|f|^q=\|f\|_q^q$; dividing by the positive number $c^q$ gives the claimed bound.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.Hypercontractivity.cubeLpNorm_rpow`.
