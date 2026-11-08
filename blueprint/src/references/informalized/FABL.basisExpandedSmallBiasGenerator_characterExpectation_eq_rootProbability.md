<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.basisExpandedSmallBiasGenerator_characterExpectation_eq_rootProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character expectation as root probability

**Claim.** For a nonzero coefficient vector, the character expectation of the basis-expanded generator equals the proportion of field elements that are roots of its associated polynomial.

**Proof.** Use the character-expectation formula for a field-pairing generator: when a nonzero polynomial evaluates at each field element to the corresponding field-pairing coefficient, the expectation over the two field variables is the polynomial's number of roots divided by the field size (\(\texttt{fieldPairingGenerator\_characterExpectation\_eq\_rootProbability}\)). Here the basis-expanded polynomial is nonzero because the coefficient vector is nonzero (\(\texttt{basisExpandedSmallBiasPolynomial\_ne\_zero}\)). Its evaluation at each $r$ is exactly the field-pairing coefficient of the basis-expanded family (\(\texttt{basisExpandedSmallBiasPolynomial\_eval}\)). These facts meet the formula's hypotheses, and substituting this polynomial and family gives the claimed root proportion.

**Key facts.** `FABL.basisExpandedSmallBiasPolynomial_ne_zero`, `FABL.basisExpandedSmallBiasPolynomial_eval`, `FABL.fieldPairingGenerator_characterExpectation_eq_rootProbability`.
