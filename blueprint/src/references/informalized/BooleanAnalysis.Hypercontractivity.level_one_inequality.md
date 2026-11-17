<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/Influence.lean :: BooleanAnalysis.Hypercontractivity.level_one_inequality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Fourier Weight Bound

**Claim.** For a Boolean indicator $f$ with positive mean $\alpha$, its level-one Fourier weight is at most $2\alpha^2\ln(1/\alpha)$.

**Proof.** Write $\alpha=\mathbb E[f]$. Since $f$ takes only $0$ and $1$, it is pointwise bounded above by the constant function $1$; monotonicity of expectation and the expectation of a constant give $\alpha\leq1$. Together with $\alpha>0$, this implies $\ln(1/\alpha)\geq0$. The level-one weight is nonnegative. If it is zero, the claimed bound follows from nonnegativity of the right-hand side. Otherwise, choose a unit vector $a$ whose associated linear form has correlation with $f$ equal to the square root of the level-one weight (existence of a unit linear form attaining that correlation). Apply the indicator linear-form inequality to this $a$. The correlation identity turns its left side into the square of that square root, namely the level-one weight, yielding the result.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.ThresholdFunctions.expect_const`, `BooleanAnalysis.ThresholdFunctions.weightLevel_nonneg`, `BooleanAnalysis.ThresholdFunctions.exists_unit_linear_form`, `BooleanAnalysis.Hypercontractivity.indicator_linear_form_sq_le`.
