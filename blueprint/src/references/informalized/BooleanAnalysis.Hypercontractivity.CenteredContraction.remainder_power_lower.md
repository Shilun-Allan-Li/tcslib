<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_power_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power controlled by affine remainder

**Claim.** For every $q\ge2$ and real $x$, $|x|^q$ is bounded by $2^q(q+3)$ times the affine remainder $|1+x|^q-1-qx$.

**Proof.** Write $R=|1+x|^q-1-qx$. The quadratic lower bound (`remainder_lower`) gives $x^2\le R$, in particular $R\ge0$. Split into two ranges. If $|x|\le1$, monotonicity of powers in the exponent gives $|x|^q\le x^2$. Also $2^q\ge1$ and $q+3\ge1$, so $1\le2^q(q+3)$. Combining these with $x^2\le R$ proves the claim in this range.

If $|x|>1$, then $|x|\le x^2$ and hence $|x|^q\ge|x|$. The quadratic lower bound, multiplied by $q+2$, together with $q\ge2$ and these comparisons, yields $|1+x|^q+1\le(q+3)R$. The translated-power estimate (`translated_power_bound`) gives $|x|^q\le2^q(|1+x|^q+1)$. Combining the last two inequalities proves the desired bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_lower`, `BooleanAnalysis.Hypercontractivity.CenteredContraction.translated_power_bound`.
