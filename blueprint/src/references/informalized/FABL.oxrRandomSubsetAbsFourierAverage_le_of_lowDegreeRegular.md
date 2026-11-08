<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrRandomSubsetAbsFourierAverage_le_of_lowDegreeRegular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree Fourier average bound

**Claim.** Under the stated oddness, nonnegativity, and low-degree regularity assumptions, every set $S$ of at most $t$ coordinates has expected absolute Fourier coefficient at $S\cap K$ at most $R$.

**Proof.** Set $q=1-\delta$, so $0\le q\le1$. For each sampled set $K$, put $J=S\cap K$. If $J$ is nonempty, then $J\subseteq S$ gives $|J|\le|S|\le t$, so low-degree regularity bounds $|\widehat f(J)|$ by $R$. If $J$ is empty, oddness makes its Fourier coefficient zero: the empty set has even cardinality, so `FABL.fourierCoeff_even_eq_zero_of_odd` applies. In either case $|\widehat f(S\cap K)|\le R$. The subset weights at parameter $q$ are nonnegative (`FABL.deltaRandomSubsetWeight_nonneg`), so multiplying each pointwise bound by its weight and summing preserves the inequality. The weights sum to one (`FABL.sum_deltaRandomSubsetWeight`), hence the resulting weighted average is at most $R$.

**Key facts.** `FABL.deltaRandomSubsetWeight_nonneg`, `FABL.fourierCoeff_even_eq_zero_of_odd`, `FABL.sum_deltaRandomSubsetWeight`.
