<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.sharpLevelOneInequality_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero mean forces zero level-one weight

**Claim.** If $f$ takes values in $[0,1]$ on the Boolean cube and has mean zero, then its level-one Fourier weight is zero.

**Proof.** Since $f$ is pointwise nonnegative and has mean zero on the finite cube, it vanishes at every point. Thus all its Fourier coefficients vanish. The level-one weight is the sum of the squares of the singleton Fourier coefficients, so it is zero.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`.
