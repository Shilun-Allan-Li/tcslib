<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_two_point_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Two Point Inequality

**Claim.** Under the stated hypotheses, the squared weighted mean plus the bias correction is at most the weighted $p$-power expression raised to $2/p$.

**Proof.** First, the bias coefficient $r$ is less than $1$ by the bias-coefficient bound (`bias_coefficient_pos_lt_one`). The quantity
\[
2\alpha^p\beta^p(1-r)(|u||v|-uv)
\]
is nonnegative: the power factors are positive, $1-r>0$, and $|uv|\ge uv$. Expanding both squares shows that the expression on the left of the desired inequality equals
\[
(\alpha^p|u|+\beta^p|v|)^2+r\alpha^p\beta^p(|u|-|v|)^2
-2\alpha^p\beta^p(1-r)(|u||v|-uv).
\]
Dropping the nonnegative subtracted term bounds it above by the first two terms in this display. Apply the nonnegative biased two point inequality (`nonnegative_biased_two_point_le`) to $|u|$ and $|v|$, which are nonnegative, to bound those terms by $(\alpha^p|u|^p+\beta^p|v|^p)^{2/p}$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.nonnegative_biased_two_point_le`.
