<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Centered.lean :: BooleanAnalysis.Hypercontractivity.CenteredContraction.pow_remainder_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integer-power remainder bound

**Claim.** For every natural number $m$ and every real $x$ with $|x|\le1$, the remainder $(1+x)^m-1-mx$ is at most $(2^m-1-m)x^2$.

**Proof.** Proceed by induction on $m$. The case $m=0$ is immediate. For the induction step, write the next remainder exactly as
\[
(1+x)\bigl((1+x)^m-1-mx\bigr)+mx^2.
\]
The assumption $|x|\le1$ gives $0\le1+x\le2$. Also, $2^m-1-m\ge0$, since Bernoulli's inequality gives $1+m\le(1+1)^m=2^m$. Thus the induction hypothesis can be multiplied by the nonnegative factor $1+x$, and the resulting quadratic term can be bounded by replacing $1+x$ with $2$. The upper bound becomes
\[
2(2^m-1-m)x^2+mx^2=(2^{m+1}-1-(m+1))x^2,
\]
which is the required estimate at the next integer.
