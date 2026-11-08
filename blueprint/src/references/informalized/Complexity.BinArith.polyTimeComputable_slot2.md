<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_slot2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-Slot Projection

**Claim.** The function that decodes a bit string into two components, takes the second component, decodes it again, and returns that decoding’s first component—using the empty word when a decoding fails—is polynomial-time computable.

**Proof.** The first total projection, which returns the second component of a decoded pair and defaults to the empty word on failure, is polynomial-time computable. Applying that same projection to its output is polynomial-time computable as well: polynomial-time computable functions are closed under composition ( `Complexity.PolyTimeComputable.comp`). The resulting composite is exactly the stated second-slot projection.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairFstD`.
