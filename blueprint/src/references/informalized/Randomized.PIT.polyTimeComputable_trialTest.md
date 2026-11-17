<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.polyTimeComputable_trialTest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Trial Testing

**Claim.** The Boolean function that decodes a bit string into its two components, applies the trial test to them, and returns the result as a one-bit string is computable in polynomial time.

**Proof.** First extract the fields of the first decoded component that specify the variable count and the two gates, and extract the second decoded component as the random string. The slot-extraction and projection procedures are polynomial-time computable ( `polyTimeComputable_slot2`, `polyTimeComputable_slot3`, `polyTimeComputable_slot4`, `polyTimeComputable_pairFstD`, and `polyTimeComputable_pairSndD`); composition gives polynomial-time procedures for each field. Pair encoding preserves polynomial-time computability, so assemble the shared input from the variable count, random string, and parameter field. Append each gate field in turn and apply modular gate evaluation; both resulting values are polynomial-time computable by composition with `polyTimeComputable_evalModW`. Pair-encode these values and apply the polynomial-time equality test `polyTimeComputable_beq`. Finally, the definition of the trial test identifies this computed Boolean with the requested output, and the Boolean-valued procedure returns it as a one-bit string by `polyTimeComputable_test_app`.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot2`, `Complexity.BinArith.polyTimeComputable_slot4`, `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Randomized.PIT.polyTimeComputable_evalModW`, `Complexity.BinArith.polyTimeComputable_beq`, `Complexity.BinArith.polyTimeComputable_app`, `Complexity.BinArith.polyTimeComputable_test_app`.
