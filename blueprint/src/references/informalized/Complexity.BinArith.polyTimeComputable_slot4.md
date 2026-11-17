<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_slot4 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-Slot Projection

**Claim.** The function that applies the total second projection three times to a bit string is polynomial-time computable.

**Proof.** By the third-slot result, applying the total second projection twice is polynomial-time computable. The projection itself is also polynomial-time computable, and polynomial-time computability is closed under composition ( `Complexity.PolyTimeComputable.comp`). Composing the projection with the twofold iteration yields the stated threefold iteration.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairSndD`.
