<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.polyTimeComputable_pitToZerop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time PIT Pair Transformation

**Claim.** The PIT pair transformation is polynomial-time computable: it returns the prescribed reduction string when both components are valid and their decoded variable strings have equal length, and returns the empty string otherwise.

**Proof.** The validity test on each decoded component is polynomial-time computable by composing the validity procedure with the corresponding component decoder. For the remaining condition, extract both components, apply the unary head transducer to each, pair the resulting words, and apply the polynomial-time length-equality test; the pairing identities ensure that this tests exactly equality of the two decoded variable-string lengths. The conjunction closure combines the two validity outputs and this length test into the required Boolean condition. The two branches of the transformation are polynomial-time computable: the valid branch is the prescribed reduction construction, and the invalid branch is the constant empty word. The polynomial-time conditional closure therefore proves the result.

**Key facts.** `Complexity.BinArith.polyTimeComputable_test_app`, `Randomized.PIT.polyTimeComputable_validW`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_uHead`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.polyTimeComputable_lenEq`, `Complexity.polyTimeComputable_and`, `Randomized.PIT.polyTimeComputable_subW`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`.
