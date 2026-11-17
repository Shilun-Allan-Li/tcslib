<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.stableInfluence_term_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence Summand Bound

**Claim.** If $\rho\ge0$ and $i\in S$, then the summand $\rho^{|S|-1}\widehat f(S)^2$ is at most the stable influence of $f$ at parameter $\rho$ and coordinate $i$.

**Proof.** The stable influence is the sum of these terms over all coordinate subsets containing $i$. Every term is nonnegative, because $\rho\ge0$ and each Fourier coefficient is squared. Since $S$ is among the indexing subsets, its summand is at most the whole sum.
