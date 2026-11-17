<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialIntersect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of Both Special Bits Being True

**Claim.** Under the uniform law on hard samples, the event that both special bits are true has probability $1/4$.

**Proof.** Write the event as the product condition that the special coordinate is unrestricted, both special bits equal true, and the other-coordinate vector is unrestricted. The product-measure formula for hard samples (`hardSample_measureReal_fieldProduct`) factors its probability into the four component probabilities. The unrestricted special coordinate and other-coordinate vector each contribute $1$ (`uniformFin_univ` and `uniformDisjointCoordinateVector_univ`), while each true special bit contributes $1/2$ (`uniformBool_singleton`). Thus the probability is $1\cdot(1/2)\cdot(1/2)\cdot1=1/4$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.hardSample_measureReal_fieldProduct`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_univ`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_univ`.

**Caveat.** The supplied informal statement describes a different distribution. This account follows the formal theorem and proof source, which establish the probability of the event that both special bits are true.
