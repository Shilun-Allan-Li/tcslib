<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_residual_cond_iIndepFun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of residual-conditioning pairs

**Claim.** Under the uniform law on disjoint-coordinate vectors, the pairs consisting of each coordinate's residual bit and conditioning bit form a mutually independent family.

**Proof.** The coordinate projections of a uniform disjoint-coordinate vector are mutually independent, as stated by `uniformDisjointCoordinateVector_iIndepFun`. Apply the preservation of mutual independence under coordinatewise measurable maps: at each coordinate, map its disjoint-coordinate label to the prescribed pair of residual and conditioning bits. The resulting family is therefore mutually independent. Unfolding the definitions of those two bits identifies this mapped family with the one in the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_iIndepFun`.
