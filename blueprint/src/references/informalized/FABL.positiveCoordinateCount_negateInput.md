<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.positiveCoordinateCount_negateInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count Under Sign Negation

**Claim.** Negating a sign vector changes its positive coordinate count to $n$ minus its original positive coordinate count.

**Proof.** Negating each sign reverses its sign value, so the sum of the sign values of the negated vector is the negative of the original sum. For any sign vector, that sum equals twice its positive coordinate count minus $n$ (\(\texttt{sum\_signValue\_eq\_two\_mul\_positiveCoordinateCount\_sub}\)). Applying this identity to both vectors and equating the sums gives, over the reals, that the two positive counts add to $n$. These counts are natural numbers, so the same equality holds in the naturals; rearranging yields the claimed subtraction formula.

**Key facts.** `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`, `FABL.positiveCoordinateCount_le`.
