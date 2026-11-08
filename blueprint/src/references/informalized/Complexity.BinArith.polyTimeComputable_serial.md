<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_serial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-State Serial Output in Polynomial Time

**Claim.** For the fixed finite-state transition and output functions and initial state, the function that decodes two bit strings, right-pads them, and emits the serial output over the resulting sequence of bit pairs is polynomial-time computable.

**Proof.** First compute the padded sequence of bit pairs from the two decoded components and flatten each pair into its two bits. This input transformation is polynomial-time computable by `polyTimeComputable_zipStream`. Then apply the finite-state transducer with transition and output functions that process each pair of input bits together: `polyTimeComputable_transduce` establishes that this transduction is polynomial-time computable because the state space is finite and has decidable equality. The identity `transduce_pairs` states that, on a flattened list of paired bits and with initial transducer state $(\text{none},s)$, the transducer's output is exactly `serialOut` on the original sequence of pairs. Thus the composition computes the required serial output in polynomial time.

**Key facts.** `Complexity.BinArith.polyTimeComputable_zipStream`, `Complexity.polyTimeComputable_transduce`, `Complexity.BinArith.transduce_pairs`, `Complexity.PolyTimeComputable.comp`.
