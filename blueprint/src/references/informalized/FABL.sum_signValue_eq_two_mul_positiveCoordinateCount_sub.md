<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Sum and Positive Coordinates

**Claim.** For a sign vector of length $n$, the sum of its coordinate signs is twice the number of coordinates equal to $1$, minus $n$.

**Proof.** Each coordinate sign is $1$ when that coordinate equals $1$, and $-1$ otherwise (`signValue_eq_ite`). For either possibility, this value equals twice the indicator of being $1$, minus $1$. Summing over all coordinates therefore gives twice the sum of those indicators minus $n$. The indicator sum is exactly the number of coordinates equal to $1$, by the definitions of the positive-coordinate set and its cardinality.

**Key facts.** `FABL.signValue_eq_ite`.
