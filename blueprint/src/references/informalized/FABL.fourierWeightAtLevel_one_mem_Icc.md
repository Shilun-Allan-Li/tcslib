<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.fourierWeightAtLevel_one_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Fourier Weight Bounds

**Claim.** For a Boolean sign function, the sum of squared singleton Fourier coefficients of its real-valued representation lies between zero and one.

**Proof.** The lower bound follows because the level-one weight is a sum of squares. For the upper bound, restrict the sum of squared Fourier coefficients over all subsets to the singleton subsets; every omitted term is nonnegative. Parseval's identity for a Boolean sign function says that the full sum is one (`sum_sq_fourierCoeff_eq_one`). Thus the level-one sum is at most one.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`.
