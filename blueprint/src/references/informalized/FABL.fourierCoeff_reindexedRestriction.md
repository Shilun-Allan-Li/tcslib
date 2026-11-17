<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.fourierCoeff_reindexedRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of reindexed restrictions

**Claim.** For a restriction with fixed signs outside $J$ and free coordinates reindexed by a bijection $e:[k]\to J$, its Fourier coefficient at $S\subseteq[k]$ equals the restriction’s indexed Fourier coefficient at $e(S)$.

**Proof.** Apply the Fourier-coefficient reindexing identity to the function of the free coordinates obtained by restricting the original function with the fixed assignment outside $J$ (\(\texttt{FABL.fourierCoeff_reindexSignCube}\)). The image of $S$ under the reindexing is exactly the mapped set $e(S)$, and the resulting indexed coefficient is the one in the claim.

**Key facts.** `FABL.fourierCoeff_reindexSignCube`.
