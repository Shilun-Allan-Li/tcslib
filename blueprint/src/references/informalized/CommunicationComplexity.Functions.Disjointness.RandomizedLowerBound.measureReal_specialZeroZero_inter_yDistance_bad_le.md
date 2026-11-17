<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialZeroZero_inter_yDistance_bad_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad-Event Mass for Bob’s Special Bit

**Claim.** If the total claimed information is at most $2\gamma^4/3$ and $\gamma>0$, then the measure of samples with both special bits zero and with Bob’s conditional special-bit law more than $\gamma$ from uniform is at most $\gamma/2$.

**Proof.** Pass to the dual protocol, which exchanges Alice’s and Bob’s roles. Its claimed information equals that of the original protocol (`claimInfo_dualProtocol`), so it satisfies the same information bound. Apply the established bound for Alice’s conditional special-bit law (`measureReal_specialZeroZero_inter_xDistance_bad_le`) to the dual protocol. The defining correspondence between Alice’s distance for the dual protocol and Bob’s distance for the original protocol identifies the two bad-event measures (`volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance`), yielding the claimed bound.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.claimInfo_dualProtocol`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialZeroZero_inter_xDistance_bad_le`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance`.
