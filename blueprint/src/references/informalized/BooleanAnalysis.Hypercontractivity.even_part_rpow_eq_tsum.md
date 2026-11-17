<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.even_part_rpow_eq_tsum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Part of the Generalized Binomial Series

**Claim.** For real $s,x$ with $|x|<1$, the average of $(1+x)^s$ and $(1-x)^s$ equals the generalized binomial series retaining only its even-degree terms.

**Proof.** The generalized binomial expansion converges to $(1+x)^s$ when $|x|<1$ (`hasSum_choose_rpow`), and the same expansion at $-x$ converges to $(1-x)^s$, since $|-x|<1$. Adding these two convergent series and dividing by $2$ gives a series whose $k$th term is $\bigl(\binom{s}{k}x^k+\binom{s}{k}(-x)^k\bigr)/2$.

For even $k=2j$, the two powers agree, so the term is $\binom{s}{2j}x^{2j}$. For odd $k$, they cancel. The even-indexed series is summable (`summable_choose_even`), and the odd part sums to zero. Thus the resulting sum is precisely $\sum_{j=0}^{\infty}\binom{s}{2j}x^{2j}$, proving the identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.hasSum_choose_rpow`, `BooleanAnalysis.Hypercontractivity.summable_choose_even`.
