<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.polyTimeComputable_evenLength -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length Parity

**Claim.** The function that outputs one for an even-length input and zero for an odd-length input is polynomial-time computable.

**Proof.** Scan the input with a two-state transducer that flips its state on every bit and emits the flipped state at each step. Starting from false, its final state after $w$ has been read is true exactly when the length of $w$ is odd; this follows by induction on the list. Consequently, the last emitted bit is true exactly for odd length (and for the empty list the default final bit is false). The transducer is polynomial-time computable, and extracting its last bit preserves polynomial-time computability. Negating that bit gives true exactly for even length, as required.

**Key facts.** `Complexity.polyTimeComputable_transduce`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.polyTimeComputable_lastBit`, `Complexity.polyTimeComputable_not`.
