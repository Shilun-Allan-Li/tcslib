<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.Tensorization.eLpNorm_top_le_of_forall_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# High Moments Bound the Essential Supremum

**Claim.** If a real-valued function is almost everywhere strongly measurable and its $L^n$ seminorm is bounded by $C$ for every sufficiently large natural number $n$, then its $L^\infty$ seminorm is at most $C$.

**Proof.** If $C=\infty$, the conclusion is immediate. Otherwise, to show that the essential supremum is at most $C$, it suffices to show that for every finite $\varepsilon>C$, the set where $|f|\ge\varepsilon$ has measure zero. Markov's inequality bounds this set's measure, for each positive integer $n\ge N$, by $\varepsilon^{-n}\|f\|_{L^n}^n\le (C/\varepsilon)^n$. Since $C/\varepsilon<1$, these bounds tend to zero as $n$ tends to infinity, so the set has measure zero. Thus $|f|<\varepsilon$ almost everywhere for every such $\varepsilon$. Taking the infimum over these thresholds gives an essential-supremum bound of $C$.
