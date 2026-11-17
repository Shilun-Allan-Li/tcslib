<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.summable_choose_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even binomial series summability

**Claim.** For real $s,x$ with $|x|<1$, the series with terms $\binom{s}{2k}x^{2k}$ is summable.

**Proof.** The generalized binomial series has sum $(1+x)^s$ when $|x|<1$ (\texttt{BooleanAnalysis.Hypercontractivity.hasSum\_choose\_rpow}), hence its terms form a summable sequence. Restrict that series to the indices of the form $2k$. The map $k\mapsto2k$ is injective, so the subseries of even-indexed terms is summable as well.

**Key facts.** `BooleanAnalysis.Hypercontractivity.hasSum_choose_rpow`.
