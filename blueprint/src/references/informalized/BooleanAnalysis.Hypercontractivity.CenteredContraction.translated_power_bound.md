<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.translated_power_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translated absolute-power bound

**Claim.** For every real $q\ge0$ and every real $x$, $|x|^q\le 2^q(|1+x|^q+1)$.

**Proof.** The triangle inequality gives $|x|\le |1+x|+1$. Split according to whether $|1+x|\le1$. In that case $|x|\le2$, so monotonicity of the real power for nonnegative bases and exponent $q\ge0$ gives $|x|^q\le2^q$, which is at most the desired right-hand side. Otherwise $1<|1+x|$, and hence $|x|\le 2|1+x|$. Raising to the power $q$ and using $(2|1+x|)^q=2^q|1+x|^q$ gives the result, since $|1+x|^q\le |1+x|^q+1$.
