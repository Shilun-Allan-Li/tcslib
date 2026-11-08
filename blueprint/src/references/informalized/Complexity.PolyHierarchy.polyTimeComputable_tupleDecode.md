<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.polyTimeComputable_tupleDecode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time recursive pair decoding

**Claim.** If the base and decoder maps, applied to the two decoded components of an encoded pair, are polynomial-time computable, then every fixed-level recursive tuple decoding is polynomial-time computable.

**Proof.** Proceed by induction on the level. At level zero the map is exactly the assumed base map. For the successor step, first form two polynomial-time transformations of an input pair: one pairs its first decoded component with the first component decoded from its second component; the other pairs that same first component with the second component decoded from its second component. These are polynomial-time by the projection and pairing closure results. Apply the induction hypothesis to the first transformation. Apply the assumed decoder map to the second, using composition. Pair the two resulting words; this remains polynomial-time. By the recursive definition of tuple decoding, this composite is exactly the next-level map.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`.
