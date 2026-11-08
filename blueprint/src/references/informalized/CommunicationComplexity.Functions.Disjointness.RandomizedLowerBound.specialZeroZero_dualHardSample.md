<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialZeroZero_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of the all-zero event

**Claim.** A hard sample’s dual has both special bits false exactly when the original sample has both special bits false.

**Proof.** Membership in the all-zero event means that both special fields are false. Dualization exchanges the two fields: the dual’s Alice bit is the original Bob bit, and the dual’s Bob bit is the original Alice bit. Therefore both dual fields are false exactly when both original fields are false; exchanging the order of the two conditions does not change their conjunction.
