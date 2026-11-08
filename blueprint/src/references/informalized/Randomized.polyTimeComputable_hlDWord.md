<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.polyTimeComputable_hlDWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length-Limited Word Construction

**Claim.** The function sending $z$ to the length-limited fourfold iteration of the tail transducer on the decoded first component is polynomial-time computable.

**Proof.** The proof first establishes a polynomial bound for the iterates of the step map. This map preserves the decoded first component, and its output length is bounded by the current input length plus a fixed multiple of that component's length and one: the two cases in its definition either retain the second component or replace it by four copies, with the length test controlling the latter case. The decoded-component length bound and the pair-encoding length formula supply the estimates. The contextual iteration bound then gives a polynomial bound for every iterate used by the loop, and the polynomial-time loop theorem applies to the step map. Separately, the tail transducer on the decoded first component is polynomial-time computable by composition. Pairing two copies of this output and the fixed one-bit seed produces the loop's initial input. Finally, extracting the third slot (two successive second-component decodings) from the loop result is polynomial-time computable, and gives exactly the claimed function.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.length_pair_components_le`, `Turing.length_pairEncode`, `Complexity.BinArith.forLoop_bound_of_ctx`, `Randomized.polyTimeComputable_pow4Step`, `Complexity.BinArith.polyTimeComputable_forLoop`, `Complexity.BinArith.polyTimeComputable_uRest`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_const`, `Complexity.BinArith.polyTimeComputable_slot3`.
