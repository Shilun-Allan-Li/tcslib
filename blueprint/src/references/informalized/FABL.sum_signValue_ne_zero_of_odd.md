<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.sum_signValue_ne_zero_of_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero Sign Sum in Odd Dimension

**Claim.** If $n$ is odd, then the sum of the coordinate signs of any sign vector of length $n$ is nonzero.

**Proof.** By the sign-sum formula (FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub), a zero sum would imply that twice the number of positive coordinates equals $n$. Write the odd integer $n$ as $2k+1$. This would make $2$ times an integer equal to $2k+1$, which is impossible because the left side is even and the right side is odd. Thus the sign sum cannot be zero.

**Key facts.** `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`.
