<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.arcsinOddPowerSeries_hasSum_of_arcsinSeries -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Power Series Sum Transfer

**Claim.** If the series whose $j$th term is the arcsine series coefficient of index $j$ multiplied by $z^{2j+1}$ has sum $a$, then the series whose $k$th term is the coefficient of exponent $k$ multiplied by $z^k$ also has sum $a$.

**Proof.** Group the terms of the latter series by writing each natural exponent uniquely as $2j+r$, where $r$ is either $0$ or $1$. For each fixed $j$, the two terms in this group sum to the $j$th term of the given series: the even-exponent coefficient is zero, while the odd-exponent coefficient equals the arcsine series coefficient of index $j$. The sum of the norms of all grouped terms is finite: each group has only two terms, and its sum of norms equals the norm of the corresponding given-series term. The given series is summable, so these grouped norms are summable as well. Consequently, the terms can be summed over the pairs $(j,r)$ and then grouped by $j$; the resulting sum equals the given sum $a$. Reindexing the pairs by their associated natural exponent gives the desired series and preserves its sum.
