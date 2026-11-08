<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.originalBLRTester_acceptanceProbability_odd_noise_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd noisy-function acceptance bound

**Claim.** Under the stated parameter, range, and stable-influence assumptions, the original three-query BLR tester accepts the odd part of the $\rho$-noise of $f$ with probability at most $\frac12+\frac{\sqrt{\varepsilon}}2$.

**Proof.** Write $g$ for the odd part of the $\rho$-noise of $f$. We first bound each Fourier coefficient of $g$. If a set $S$ has even cardinality, the Fourier coefficient of an odd part at $S$ vanishes (\texttt{FABL.fourierCoeff\_oddPart\_of\_even}), and hence is at most $\sqrt{\varepsilon}$. If $|S|$ is odd, then $S$ is nonempty; choose $i\in S$. The summand indexed by $S$ in the stable influence at $i$ is nonnegative and no greater than the entire sum. The small-influence assumption thus bounds it by $\varepsilon$.

Because $0\leq\rho^2\leq1-\varepsilon$, comparison of powers gives $\rho^{2|S|}\leq(1-\varepsilon)^{|S|-1}$. Multiplying by the squared Fourier coefficient of $f$ and using the stable-influence bound shows that $(\rho^{|S|}\widehat f(S))^2\leq\varepsilon$. The odd-part Fourier coefficient at odd $S$ equals the original coefficient of the noisy function, and noise multiplies that coefficient by $\rho^{|S|}$ (\texttt{FABL.fourierCoeff\_oddPart\_of\_odd}, \texttt{FABL.fourierCoeff\_noiseOperator}). Therefore $|\widehat g(S)|\leq\sqrt{\varepsilon}$, so in all cases $\widehat g(S)\leq\sqrt{\varepsilon}$.

The original BLR acceptance probability is $\frac12+\frac12\sum_S\widehat g(S)^3$ (\texttt{FABL.originalBLRTester\_acceptanceProbability\_eq\_fourierSum}). Termwise, $\widehat g(S)^3\leq\sqrt{\varepsilon}\,\widehat g(S)^2$. Summing and applying the Fourier square-sum bound for a function valued in $[-1,1]$, $\sum_S\widehat g(S)^2\leq1$ (\texttt{FABL.BoundedCubeFunction.sum\_sq\_fourierCoeff\_le\_one}), gives $\sum_S\widehat g(S)^3\leq\sqrt{\varepsilon}$. Substitution in the acceptance identity proves the asserted bound.

**Key facts.** `FABL.fourierCoeff_oddPart_of_even`, `FABL.fourierCoeff_oddPart_of_odd`, `FABL.fourierCoeff_noiseOperator`, `FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`, `FABL.originalBLRTester_acceptanceProbability_eq_fourierSum`.
