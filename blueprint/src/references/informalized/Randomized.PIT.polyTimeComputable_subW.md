<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.polyTimeComputable_subW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Subtraction Word

**Claim.** The function forming the specified concatenation of unary-head data, shift-run outputs, a fixed tag, selected scan-index suffixes, and final zero bits is polynomial-time computable.

**Proof.** The total first and second projections are polynomial-time computable. The scan-index data after applying scan run to either projection are polynomial-time computable by composition: the scan-index selector is the first projection of the third nested total second projection. The shift-run terms are also polynomial-time computable: each is obtained by pair encoding polynomial-time data (including the unary rest of an input projection) and applying shift run. The unary head of the first projection is polynomial-time computable by composition. Taking the suffix after the first bit is polynomial-time computable, so this applies both to the first scan-index output and to the concatenation of the two scan-index outputs. Finally, the displayed definition of the subtraction word is a concatenation of these polynomial-time functions and fixed strings. Repeated closure under concatenation proves the claim.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.BinArith.polyTimeComputable_app`, `Randomized.PIT.polyTimeComputable_scanRun`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.polyTimeComputable_uRest`, `Randomized.PIT.polyTimeComputable_shiftRun`, `Complexity.BinArith.polyTimeComputable_uHead`, `Complexity.polyTimeComputable_tail`, `Complexity.PolyTimeComputable.append`.
