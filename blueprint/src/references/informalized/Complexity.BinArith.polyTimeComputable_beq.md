<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.polyTimeComputable_beq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Equality Test

**Claim.** The function on bit strings that decodes the two components of a pair, interprets each as a natural number with the first bit least significant, and returns the one-bit word $[1]$ when the values are equal and $[0]$ otherwise, is polynomial-time computable.

**Proof.** Compute the comparison that tests whether the first decoded value is at most the second, and also compute that same comparison after swapping the decoded components. Both computations are polynomial-time: the swap is polynomial-time, and composition preserves polynomial time. Their conjunction is polynomial-time as well (`Complexity.BinArith.polyTimeComputable_le`, `Complexity.polyTimeComputable_pairSwap`, `Complexity.PolyTimeComputable.comp`, and `Complexity.polyTimeComputable_and`). For natural numbers, both inequalities hold exactly when the values are equal. Thus the conjunction is the required equality bit.

**Key facts.** `Complexity.BinArith.polyTimeComputable_le`, `Complexity.polyTimeComputable_pairSwap`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_and`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
