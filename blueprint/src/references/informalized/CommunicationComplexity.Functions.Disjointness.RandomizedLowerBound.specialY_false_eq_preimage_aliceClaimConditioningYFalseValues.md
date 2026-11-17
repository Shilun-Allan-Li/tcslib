<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialY_false_eq_preimage_aliceClaimConditioningYFalseValues -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bob’s false-bit event as a preimage

**Claim.** The event that Bob’s special bit is false equals the preimage, under the conditioning variable, of the triples whose Bob-bit function is false at the special coordinate.

**Proof.** Take any sample $\omega$. Membership in the left-hand set means its special-$Y$ value is false. On the right, the conditioning triple is $(T,X_{<T},Y_{\ge T})$, and the defining condition asks whether its last component evaluated at $T$ is false. The fact that $Y_{\ge T}(T)$ equals Bob’s special bit (the special-coordinate evaluation identity, `yGeSpecial_specialCoordinate`) makes these conditions equivalent for every $\omega$. Thus the sets are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yGeSpecial_specialCoordinate`.
