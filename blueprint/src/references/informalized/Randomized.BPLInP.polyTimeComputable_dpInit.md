<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.polyTimeComputable_dpInit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Initialization

**Claim.** For every finite nondeterministic Turing machine $N$ over bits and natural numbers $c,B,e$, the function mapping a bit string to its initialized dynamic-programming encoding is polynomial-time computable.

**Proof.** The context word is polynomial-time computable: it pairs the input with the radius word and the code word, using the polynomial-time identity, radius, and code-generation results (Complexity.polyTimeComputable_id, Randomized.BPLInP.polyTimeComputable_radius, Randomized.BPLInP.polyTimeComputable_codesW, and Complexity.PolyTimeComputable.pairEncode). Next, the indicator for the accepting-configuration language is polynomial-time computable because that language is in log space (Complexity.Codec.acceptLang_mem and Randomized.BPLInP.polyTimeComputable_indicator_of_LOGSPACE). Decoding the components needed for this membership test and selecting either the one-bit acceptance word or the empty word preserves polynomial-time computability (Complexity.polyTimeComputable_pairFstD, Complexity.polyTimeComputable_pairSndD, Complexity.polyTimeComputable_ite, and Complexity.polyTimeComputable_const). Thus the initialization entry function is polynomial-time computable. Apply the polynomial-time map operation to these entries, with input assembled from the context and code words, and pair the resulting map with the context. Closure under pairing and the map operation (Complexity.BinArith.polyTimeComputable_mapW and Complexity.PolyTimeComputable.pairEncode) proves that the full initialization encoding is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_id`, `Randomized.BPLInP.polyTimeComputable_radius`, `Randomized.BPLInP.polyTimeComputable_codesW`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.Codec.acceptLang_mem`, `Randomized.BPLInP.polyTimeComputable_indicator_of_LOGSPACE`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_const`, `Complexity.BinArith.polyTimeComputable_mapW`.
