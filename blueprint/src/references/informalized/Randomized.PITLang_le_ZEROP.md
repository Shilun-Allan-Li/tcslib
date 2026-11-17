<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PITLang_le_ZEROP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction to Circuit Zero Testing

**Claim.** There is a polynomial-time many-one reduction from the language of paired encodings of well-formed circuits on the same inputs with equal associated polynomials to the language of encodings of well-formed circuits whose associated polynomial is zero.

**Proof.** Use the map `pitToZerop` as the reduction. Its polynomial-time computability is established by `polyTimeComputable_pitToZerop`, and `mem_PITLang_iff_pitToZerop` proves, for every input, that the input belongs to the circuit-equivalence language exactly when its image belongs to the zero-polynomial language. These are precisely the runtime and membership-preservation conditions for the claimed many-one reduction.

**Key facts.** `Randomized.polyTimeComputable_pitToZerop`, `Randomized.mem_PITLang_iff_pitToZerop`.
