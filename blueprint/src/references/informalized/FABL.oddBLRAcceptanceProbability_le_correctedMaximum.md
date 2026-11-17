<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.oddBLRAcceptanceProbability_le_correctedMaximum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd BLR Fourier Maximum Bound

**Claim.** The odd BLR acceptance probability is at most $\frac12+\frac12 M$, where $M$ is the maximum of zero and the Fourier coefficients indexed by odd-cardinality subsets.

**Proof.** Use the Fourier-sum formula for acceptance (\(\texttt{oddBLRAcceptanceProbability\_eq\_fourierSum}\)). For each odd-cardinality set $S$, its coefficient is at most $M$ (\(\texttt{fourierCoeff\_le\_nonnegativeOddFourierMaximum}\)). Multiplying by the nonnegative square of that coefficient gives $\widehat f(S)^3\le M\widehat f(S)^2$. Summing over odd sets bounds the cubic sum by $M$ times the odd-indexed sum of squares. The latter is bounded by the sum over all sets, since each omitted square is nonnegative. Parseval's identity says this full sum of squares is one (\(\texttt{sum\_sq\_fourierCoeff\_eq\_one}\)); also $M\ge0$ (\(\texttt{nonnegativeOddFourierMaximum\_zero\_le}\)), so the cubic sum is at most $M$. Substituting into the acceptance formula yields the stated bound.

**Key facts.** `FABL.oddBLRAcceptanceProbability_eq_fourierSum`, `FABL.fourierCoeff_le_nonnegativeOddFourierMaximum`, `FABL.nonnegativeOddFourierMaximum_zero_le`, `FABL.sum_sq_fourierCoeff_eq_one`.
