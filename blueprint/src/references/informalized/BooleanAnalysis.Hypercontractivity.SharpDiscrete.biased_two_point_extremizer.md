<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_two_point_extremizer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Two Point Extremizer

**Claim.** Under the stated normalization and parameter bounds, the specified values $u=\beta/\alpha$, $v=\alpha/\beta$, and $r$ satisfy $u\ne v$, $\alpha^p u^p+\beta^p v^p=1$, and $(\alpha^p u+\beta^p v)^2+r\alpha^p\beta^p(u-v)^2=1$.

**Proof.** Set $u=\beta/\alpha$ and $v=\alpha/\beta$. Positivity and the strict inequality $\alpha<\beta$ give $u>1$ and $v<1$, so they are unequal. The positive bases permit the usual quotient rule for real powers; consequently $\alpha^p u^p=\beta^p$ and $\beta^p v^p=\alpha^p$. Their sum is $1$ by the normalization hypothesis.

For the last identity, substitute the definitions of $u,v,r$ and use the real-power subtraction rule to rewrite the terms involving exponents $2-p$. Clearing the nonzero denominators reduces the left side to $(\alpha^p+\beta^p)^2$. The denominators are nonzero because $\alpha,\beta>0$ and $\alpha<\beta$ implies $\alpha^2\ne\beta^2$. The normalization then makes this square equal to $1$.
