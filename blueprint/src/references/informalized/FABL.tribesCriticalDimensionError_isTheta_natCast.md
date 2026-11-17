<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalDimensionError_isTheta_natCast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension error asymptotic order

**Claim.** The critical dimension error is asymptotically of order $w$ as $w$ tends to infinity.

**Proof.** The dimension error factors as $w$ times the size error, by the identity `tribesCriticalDimensionError_eq`. The size error is asymptotically of order $1$, by `tribesCriticalSizeError_isTheta_one`. The product rule for asymptotic order, applied to these two estimates, gives that the dimension error is of order $w\cdot 1=w$.

**Key facts.** `FABL.tribesCriticalDimensionError_eq`, `FABL.tribesCriticalSizeError_isTheta_one`.
