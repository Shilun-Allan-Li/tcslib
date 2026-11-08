<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.isRelevant_of_fourierCoeff_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Support Implies Relevance

**Claim.** If $i\in S$ and the Fourier coefficient of $f$ indexed by $S$ is nonzero, then $f$ has positive influence at coordinate $i$.

**Proof.** The influence at $i$ is the sum of squares of all Fourier coefficients indexed by sets containing $i$ (\texttt{FABL.influence_eq_sum_sq_fourierCoeff}). The term indexed by $S$ is one of these nonnegative summands, so the sum is at least $\widehat f(S)^2$. Since the coefficient is nonzero, its square is strictly positive; therefore the influence is positive.

**Key facts.** `FABL.influence_eq_sum_sq_fourierCoeff`.
