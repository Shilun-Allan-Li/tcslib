<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_slot3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third-Slot Projection

**Claim.** The function that applies the total second projection three times to a bit string is polynomial-time computable.

**Proof.** The total second projection is polynomial-time computable. Closure of polynomial-time computability under composition ( `Complexity.PolyTimeComputable.comp`) therefore makes two successive applications polynomial-time computable; composing once more with the same projection gives three applications, as claimed.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`.
