<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.summable_arcsinSeriesCoefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summability of Arcsine Coefficients

**Claim.** The sequence whose $j$th term is $\binom{2j}{j}/(2^{2j}(2j+1))$ is summable.

**Proof.** The coefficients are nonnegative (`FABL.arcsinSeriesCoefficient_nonneg`). To bound every partial sum, fix a finite cutoff and consider the corresponding polynomial $\sum_{j<n} c_j x^{2j+1}$, where $c_j$ is the $j$th coefficient. This polynomial is continuous, and as $x$ approaches $1$ from below it tends to the sum of the coefficients in that partial sum. For each such $x$ sufficiently near $1$, the arcsine power series identity (`FABL.arcsinSeries_hasSum_of_abs_lt_one`) applies. Its nonnegative terms imply that the finite partial sum is at most the full series value $\arcsin(x)$, which in turn is at most $\pi/2$. Passing to the limit as $x$ tends to $1$ shows that every partial sum is bounded by $\pi/2$. A nonnegative sequence with bounded partial sums is summable.

**Key facts.** `FABL.arcsinSeriesCoefficient_nonneg`, `FABL.arcsinSeries_hasSum_of_abs_lt_one`.
