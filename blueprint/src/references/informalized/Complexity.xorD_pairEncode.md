<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.xorD_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# XOR of an Encoded Pair

**Claim.** Applying total XOR to the self-delimiting pair encoding of two finite Boolean strings gives their bitwise XOR up to the length of the shorter string.

**Proof.** The pair encoding decodes to its original two components, so the total first and second projections are the original strings. The definition of total XOR then takes their positionwise XOR with `List.zipWith`, which stops when either string ends. This is precisely the asserted result.
