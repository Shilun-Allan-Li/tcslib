<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.remainder_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic remainder lower bound

**Claim.** For every $q\ge2$ and every real $x$, one has $x^2\le |1+x|^q-1-qx$.

**Proof.** Let $s=q/2\ge1$ and $u=(1+x)^2-1\ge0$. Bernoulli's inequality for real powers with exponent at least one gives $(1+u)^s\ge1+su$. Since $1+u=(1+x)^2$, this says
\[
|1+x|^q\ge 1+\frac q2\bigl((1+x)^2-1\bigr)=1+qx+\frac q2x^2.
\]
Subtracting $1+qx$ leaves at least $(q/2)x^2$, which is at least $x^2$ because $q\ge2$.
