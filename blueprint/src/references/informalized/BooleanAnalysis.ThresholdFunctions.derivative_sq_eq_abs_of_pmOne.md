<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.derivative_sq_eq_abs_of_pmOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square equals absolute value

**Claim.** If $f$ takes values in $\{-1,1\}$, then at every point and coordinate its discrete derivative satisfies $(D_i f(x))^2=|D_i f(x)|$.

**Proof.** The derivative is half the difference between two values of $f$, namely its values at the points obtained by setting coordinate $i$ to $0$ and to $1$. Each value is either $1$ or $-1$. If they agree, the derivative is $0$; if they differ, it is $1$ or $-1$. Thus the derivative belongs to $\{-1,0,1\}$, and each of these values equals its own square and has absolute value equal to that square.
