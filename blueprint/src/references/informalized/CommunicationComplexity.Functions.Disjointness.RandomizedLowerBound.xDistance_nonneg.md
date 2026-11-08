<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xDistance_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Alice’s Conditional Bit Distance

**Claim.** The total variation distance between Alice’s conditional special-bit law and the uniform bit law is nonnegative.

**Proof.** The quantity in question is the total variation distance between two probability measures: the conditional law of Alice’s special bit and the uniform law on one bit. Total variation distance between probability measures is nonnegative (`CommunicationComplexity.TVDistance.tvDistance_nonneg`), so the claimed inequality follows from the definition of Alice’s distance.

**Key facts.** `CommunicationComplexity.TVDistance.tvDistance_nonneg`.
