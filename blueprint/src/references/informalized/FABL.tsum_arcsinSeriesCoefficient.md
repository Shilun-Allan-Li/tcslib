<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.tsum_arcsinSeriesCoefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of the arcsine series coefficients

**Claim.** The sum over all natural numbers $j$ of $\frac{\binom{2j}{j}}{2^{2j}(2j+1)}$ equals $\frac{\pi}{2}$.

**Proof.** Consider the power series $F(x)=\sum_{j\ge 0} a_j x^{2j+1}$, where $a_j$ is the stated coefficient. The coefficients are nonnegative and summable (`summable_arcsinSeriesCoefficient`, `arcsinSeriesCoefficient_nonneg`). As $x$ approaches $1$ from below, each summand tends to $a_j$, and for $0<x<1$ its absolute value is at most $a_j$. Dominated convergence for series therefore gives $F(x)\to\sum_{j\ge0}a_j$. On the same interval, the arcsine power-series identity identifies $F(x)$ with $\arcsin x$ (`arcsinSeries_eq_arcsin_of_abs_lt_one`). Continuity of $\arcsin$ at $1$, together with $\arcsin(1)=\pi/2$, gives $F(x)\to\pi/2$. Uniqueness of limits yields the claimed sum.

**Key facts.** `FABL.summable_arcsinSeriesCoefficient`, `FABL.arcsinSeriesCoefficient_nonneg`, `FABL.arcsinSeries_eq_arcsin_of_abs_lt_one`.
