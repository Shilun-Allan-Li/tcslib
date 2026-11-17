<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.polyTimeComputable_bplTest_of_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Test from a Computable Run

**Claim.** If the map sending each bit string $x$ to the output of the associated dynamic-programming run is polynomial-time computable, then the function sending $x$ to the one-bit output containing the value of the test on $x$ is polynomial-time computable.

**Proof.** First extract the required run components using the polynomial-time decoders for the first and second parts of a pair (Complexity.polyTimeComputable_pairFstD and Complexity.polyTimeComputable_pairSndD). The predicate used by `pickW` is membership in the initial-configuration language. Since that language is in log space (Complexity.Codec.initLang_mem), its indicator is polynomial-time computable (Randomized.BPLInP.polyTimeComputable_indicator_of_LOGSPACE). Combining this indicator with the decoders and choosing either the extracted word or the empty word gives a polynomial-time `pickW`. Apply the polynomial-time zip-and-combine operation to the run and its decoded components, then sum the resulting contributions; closure under these operations gives polynomial-time computability of `accW` (Complexity.BinArith.polyTimeComputable_zipWithW and Randomized.BPLInP.polyTimeComputable_sumW). Finally, prepend the fixed false bit to this count, pair it with the polynomial-time computable bound word `pow2W` (Randomized.BPLInP.polyTimeComputable_pow2W), and apply the polynomial-time comparison operation (Complexity.BinArith.polyTimeComputable_lt). This produces the test bit, so the desired one-bit-output function is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.Codec.initLang_mem`, `Randomized.BPLInP.polyTimeComputable_indicator_of_LOGSPACE`, `Complexity.polyTimeComputable_ite`, `Complexity.BinArith.polyTimeComputable_zipWithW`, `Randomized.BPLInP.polyTimeComputable_sumW`, `Complexity.PolyTimeComputable.pairEncode`, `Randomized.BPLInP.polyTimeComputable_pow2W`, `Complexity.BinArith.polyTimeComputable_lt`.
