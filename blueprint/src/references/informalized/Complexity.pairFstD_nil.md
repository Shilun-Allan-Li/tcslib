<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.pairFstD_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-Word First Projection

**Claim.** The total first projection of the empty bit string is the empty bit string.

**Proof.** By definition, the total first projection applies the first-component projection to a decoded pair when decoding succeeds, and returns the empty string when decoding fails. The empty input matches none of the nonempty patterns in the decoder, so decoding returns no pair. The default value is therefore the empty string.
