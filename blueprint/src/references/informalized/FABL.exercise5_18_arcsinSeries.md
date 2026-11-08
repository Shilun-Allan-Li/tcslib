<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityLimits.lean :: FABL.exercise5_18_arcsinSeries -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arcsine power series on the closed interval

**Claim.** For every $z\in[-1,1]$, both the odd-power series with coefficients $\binom{2j}{j}/(4^j(2j+1))$ and its equivalent indexing over odd powers sum to $\arcsin z$.

**Proof.** First consider the series indexed by $j$. If $z=1$, its sum is $\pi/2$ by the endpoint identity (`FABL.arcsinSeries_hasSum_one`), which equals $\arcsin(1)$. If $z=-1$, its sum is $-\pi/2$ by the other endpoint identity (`FABL.arcsinSeries_hasSum_neg_one`), which equals $\arcsin(-1)$. In every other case the interval bounds imply $-1<z<1$, hence $|z|<1$; the interior arcsine-series identity (`FABL.arcsinSeries_hasSum_of_abs_lt_one`) gives the desired sum. Finally, the odd-power reindexing lemma (`FABL.arcsinOddPowerSeries_hasSum_of_arcsinSeries`) converts this first series into the series indexed by all natural numbers, with zero coefficients at even powers, preserving its sum.

**Key facts.** `FABL.arcsinSeries_hasSum_one`, `FABL.arcsinSeries_hasSum_neg_one`, `FABL.arcsinSeries_hasSum_of_abs_lt_one`, `FABL.arcsinOddPowerSeries_hasSum_of_arcsinSeries`.
