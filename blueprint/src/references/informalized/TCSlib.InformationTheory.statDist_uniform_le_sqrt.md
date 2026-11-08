<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/StatisticalDistance.lean :: TCSlib.InformationTheory.statDist_uniform_le_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Statistical Distance from Uniform

**Claim.** For a distribution $p$ on a nonempty finite set $\alpha$, its statistical distance from uniform is at most $\frac12\sqrt{|\alpha|\,\mathrm{collision}(p)-1}$.

**Proof.** Write $n=|\alpha|$, which is positive (`TCSlib.InformationTheory.FinDist.card_pos`). Expanding the squares and using $\sum_a p(a)=1$ gives $\sum_a(p(a)-1/n)^2=\mathrm{collision}(p)-1/n$. By Cauchy–Schwarz, $(\sum_a|p(a)-1/n|)^2\le n\sum_a|p(a)-1/n|^2$. Since squaring does not change absolute values, the right side is $n\mathrm{collision}(p)-1$. The sum of absolute deviations is nonnegative, so it is at most the square root of this bound. Uniform assigns probability $1/n$ to every point (`TCSlib.InformationTheory.FinDist.uniform_apply`); multiplying the resulting inequality by $1/2$ gives the claimed statistical-distance bound.

**Key facts.** `TCSlib.InformationTheory.FinDist.card_pos`, `TCSlib.InformationTheory.FinDist.uniform_apply`.

**Caveat.** The supplied informal statement describes two chi-square and total-variation exercises, but the formal statement and proof source establish the displayed collision-based bound; this account follows those formal materials.
