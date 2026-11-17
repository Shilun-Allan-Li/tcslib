<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.polyTimeComputable_mulU -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Multiplication in Polynomial Time

**Claim.** The function that decodes the two components of an input, repeats unary addition by appending the first component, and extracts the resulting product is polynomial-time computable.

**Proof.** First, the update that preserves the first component and appends it to the second is polynomial-time computable: decoding the components, appending the lists, and re-encoding them are polynomial-time operations (by `polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`, `PolyTimeComputable.append`, and `PolyTimeComputable.pairEncode`). To bound its iterations, use `forLoop_bound_of_ctx`. The update preserves the first decoded component, and its output length is at most the input length plus twice the length of that component. These properties follow by considering whether decoding fails or, by `pair_cases`, the input is a valid pair encoding; the encoding length formula is `length_pairEncode`. The iteration bound therefore supplies a polynomial length bound for all iterations used by `forLoop`, so `polyTimeComputable_forLoop` makes the loop polynomial-time computable. Finally, the initial nested encoding of the two decoded inputs and the empty list is polynomial-time computable by composition and pairing, and the two successive second-component projections are polynomial-time computable by `polyTimeComputable_slot3`. Composing initialization, the loop, and extraction proves the claim.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.append`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.forLoop_bound_of_ctx`, `Complexity.BinArith.pair_cases`, `Turing.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_forLoop`, `Complexity.BinArith.polyTimeComputable_slot3`.
