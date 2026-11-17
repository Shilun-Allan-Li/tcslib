<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_le_fourthMoment_levelKPolynomial_of_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment bounds the number of encoded tuples

**Claim.** If a finite type $W$ injects into the ordered quadruples of $k$-element subsets of $[n]$ whose symmetric difference is empty, then $|W|$ is at most the uniform average of the fourth power of the level-$k$ polynomial.

**Proof.** The fourth-moment identity (`expect_levelKPolynomial_pow_eq_natCard_parityTuple`) identifies the stated average with the cardinality of the set of parity tuples, viewed as a real number. The given injection from $W$ into that set implies the cardinality of $W$ is at most the cardinality of the set. Converting this natural-number inequality to a real-number inequality and applying the identity yields the result.

**Key facts.** `FABL.expect_levelKPolynomial_pow_eq_natCard_parityTuple`.
