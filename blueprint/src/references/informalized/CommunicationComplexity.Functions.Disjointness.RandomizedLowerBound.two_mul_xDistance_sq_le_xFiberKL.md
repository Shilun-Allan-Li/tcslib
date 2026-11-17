<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.two_mul_xDistance_sq_le_xFiberKL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Distance Bounded by Conditional Divergence

**Claim.** For every protocol and fiber, twice the square of the conditional special-bit law’s total variation distance from the uniform bit law is at most the real-valued relative entropy of that conditional law with respect to the uniform bit law.

**Proof.** The preceding Pinsker bound for the conditional special-bit law and the uniform bit law states that twice the square of their total variation distance is at most their real-valued relative entropy ( `two_mul_xDistance_sq_le_toReal_klDiv_uniformBool` ). By the definition of `xFiberKL`, this relative entropy is exactly the fiber’s relative-entropy quantity. Replacing it by that definition gives the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.two_mul_xDistance_sq_le_toReal_klDiv_uniformBool`.
