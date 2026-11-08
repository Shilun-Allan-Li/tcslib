<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.mean_correlationImmuneAndExample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Correlation-Immune Example

**Claim.** For every positive integer $m$, the real-valued version of the correlation-immune example on $3m$ coordinates has mean $1/2$.

**Proof.** By the empty-set Fourier identity, the mean is the Fourier coefficient at the empty set. The formula for the example’s Fourier coefficients expresses this coefficient as one half of four terms: the empty-set indicator, the indicator that the first block is empty, the indicator that the last block is empty, and minus the indicator that their symmetric difference is empty. The first indicator is $1$. Since $m>0$, both blocks are nonempty; and their symmetric difference has cardinality $2m>0$, so it too is nonempty. Thus the other three indicators vanish, giving mean $1/2$.

**Key facts.** `FABL.mean_eq_fourierCoeff_empty`, `FABL.fourierCoeff_correlationImmuneAndExample`, `FABL.card_firstTwoThirds_symmDiff_lastTwoThirds`.
