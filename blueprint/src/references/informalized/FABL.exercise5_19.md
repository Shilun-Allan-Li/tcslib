<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.exercise5_19 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moments of a correlated sign-pair sum

**Claim.** For $\rho\in[-1,1]$ and positive $n$, the normalized correlated sign sums have means zero, second moments one, and cross moment $\rho$.

**Proof.** The five asserted equalities are exactly the established moment identities for the normalized correlated pair sum: its first coordinate has mean zero (`FABL.normalizedCorrelatedPairSum_first_mean`) and second moment one (`FABL.normalizedCorrelatedPairSum_first_secondMoment`); its second coordinate has mean zero (`FABL.normalizedCorrelatedPairSum_second_mean`) and second moment one (`FABL.normalizedCorrelatedPairSum_second_secondMoment`); and the product of the two coordinates has expectation $\rho$ (`FABL.normalizedCorrelatedPairSum_crossMoment`). Together these identities give the claimed moment tuple.

**Key facts.** `FABL.normalizedCorrelatedPairSum_first_mean`, `FABL.normalizedCorrelatedPairSum_second_mean`, `FABL.normalizedCorrelatedPairSum_first_secondMoment`, `FABL.normalizedCorrelatedPairSum_second_secondMoment`, `FABL.normalizedCorrelatedPairSum_crossMoment`.
