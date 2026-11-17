<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.polyTimeComputable_gcdStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Greatest Common Divisor Step

**Claim.** The function that returns its input when the second decoded component represents zero, and otherwise encodes that component together with the binary remainder of the first component modulo it, is polynomial-time computable.

**Proof.** The second decoded component is polynomial-time computable, and so is the test that its represented value is zero. In the zero case, the function returns the input itself, a polynomial-time operation. Otherwise, encode the first and second decoded components as a pair and compute their binary remainder modulo the second component's value. Pair this result with the second component. These operations are polynomial-time computable by the remainder, projection, pairing and composition results. The polynomial-time conditional-combination result then assembles the two branches.

**Key facts.** `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.polyTimeComputable_isZero`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.BinArith.polyTimeComputable_mod`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_ite`.
