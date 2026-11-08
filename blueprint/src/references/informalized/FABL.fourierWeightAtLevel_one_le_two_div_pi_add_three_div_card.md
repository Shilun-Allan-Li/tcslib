<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/ArrowLevelOneBound.lean :: FABL.fourierWeightAtLevel_one_le_two_div_pi_add_three_div_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Explicit Level-One Weight Bound

**Claim.** If a Boolean function has equal singleton Fourier coefficients and $n>0$, then its level-one Fourier weight is at most $2/\pi+3/n$.

**Proof.** First bound the level-one weight by majority's total influence squared divided by $n$ (`fourierWeightAtLevel_one_le_totalInfluence_majority_sq_div`). Majority's total influence squared divided by $n$ is at most $2/\pi+3/n$ (`totalInfluence_majority_sq_div_card_le`). Combining the two inequalities proves the result.

**Key facts.** `FABL.fourierWeightAtLevel_one_le_totalInfluence_majority_sq_div`, `FABL.totalInfluence_majority_sq_div_card_le`.
