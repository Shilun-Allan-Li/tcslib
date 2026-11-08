<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.tseitinLiftLiteral_index_ne_exactlyThreePaddingLiteral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted and padding indices are distinct

**Claim.** The index of a literal lifted to $n+3$ coordinates differs from the index of any padding literal at one of the three added positions.

**Proof.** Assume for contradiction that the two indices are equal. Under the standard identification of the first $n$ coordinates and the three added coordinates with the two summands of a disjoint union, the lifted index is the image of the left-summand element corresponding to the original index, while the padding index is the image of the right-summand element corresponding to its position. Injectivity of this identification would make a left-summand element equal a right-summand element, which is impossible because the two summands are disjoint.
