<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Basic.lean :: KKL.influence_lowDegreePart_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of the low-degree truncation

**Claim.** The influence of coordinate $i$ on the Fourier truncation of $f$ to frequencies of size at most $d$ is at most its influence on $f$.

**Proof.** Express each influence as a sum over frequencies: the term at $S$ is $\widehat f(S)^2$ if $i\in S$, and zero otherwise (BooleanAnalysis.influence_eq_sum_fourier). It is therefore enough to compare terms frequency by frequency. If $i\notin S$, both terms are zero. If $i\in S$, the truncation's coefficient at $S$ is $\widehat f(S)$ when $|S|\le d$ and zero otherwise (KKL.fourierCoeff_lowDegreePart). Its squared coefficient is consequently either the original squared coefficient or zero, and so never exceeds the original term. Summing these inequalities proves the claim.

**Key facts.** `BooleanAnalysis.influence_eq_sum_fourier`, `KKL.fourierCoeff_lowDegreePart`.
