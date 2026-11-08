<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/MayTheorem.lean :: FABL.positiveCoordinateCount_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count Invariant Under Permutation

**Claim.** Permuting the coordinates of a sign vector does not change its number of coordinates equal to $1$.

**Proof.** Summing the sign values after the permutation gives the same sum as before, since a permutation merely reorders the coordinates. Each sum equals twice the positive coordinate count minus $n$ (\(\texttt{sum\_signValue\_eq\_two\_mul\_positiveCoordinateCount\_sub}\)). Equating these expressions shows that twice the permuted count equals twice the original count, and hence the counts are equal.

**Key facts.** `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`.
