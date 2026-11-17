<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LevelOneInequality.lean :: FABL.fourierWeightAtLevel_one_eq_zero_of_zero_one_mean_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing level-one weight

**Claim.** A function taking only the values zero and one and having mean zero has level-one Fourier weight zero.

**Proof.** The value restriction makes $f$ pointwise nonnegative. A nonnegative function on a finite probability space with mean zero vanishes everywhere, so $f=0$. Its Fourier coefficients therefore all vanish; in particular, the sum of their squares at level one is zero, using the singleton-sum formula (`fourierWeightAtLevel_one_eq_sum_singleton`).

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`.
