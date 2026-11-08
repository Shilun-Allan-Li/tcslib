<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.fourierWeightAtLevel_one_hammingUpperTailIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Weight of an Upper Tail

**Claim.** For every threshold $t$ and natural number $m$, the level-one Fourier weight of the upper-tail indicator on the $(m+1)$-dimensional cube is the square of its mean product with the normalized coordinate sum.

**Proof.** Let $M$ denote the stated mean product. Level-one Fourier weight is the sum, over coordinates $i$, of the squares of the singleton Fourier coefficients (the level-one singleton formula, `fourierWeightAtLevel_one_eq_sum_singleton`). For this indicator, each singleton coefficient equals $M/\sqrt{m+1}$ (the singleton coefficient identity, `fourierCoeff_hammingUpperTailIndicator_singleton`). Thus the sum has $m+1$ identical terms, each $M^2/(m+1)$, and so equals $M^2$. The square root is well-defined and nonzero since $m+1>0$.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.fourierCoeff_hammingUpperTailIndicator_singleton`.
