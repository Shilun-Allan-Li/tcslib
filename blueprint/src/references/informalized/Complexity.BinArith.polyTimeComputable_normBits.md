<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_normBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Binary Normalization

**Claim.** For each bit string, the binary expansion of its represented natural number is polynomial-time computable.

**Proof.** Define a chunk that examines the first bit of a string and emits its one-bit value, or emits nothing when the string is empty. This chunk is polynomial-time computable: it is a conditional built from the polynomial-time tests and operations for detecting whether any bit is true, taking the first bit, and returning a fixed empty string (`polyTimeComputable_ite`, `polyTimeComputable_any`, `polyTimeComputable_take1`, and `polyTimeComputable_const`). Apply `polyTimeComputable_emitIter` to this chunk and to the operation that drops the first bit. The orbit bound holds because after $i$ drops the remaining string has length at most the original length, as expressed by `iterate_drop_one`. Thus emitting a chunk at each position up to the input length is polynomial-time computable. The emitted chunks concatenate to the binary expansion of the represented value by `flatMap_normChunk`: each position contributes precisely its bit's place-value contribution, and the concatenation is `Nat.bits (bitsVal w)`. Taking the iteration length to be the input length plus one ensures the stated length condition, so this polynomial-time iteration computes the normalization function.

**Key facts.** `Complexity.polyTimeComputable_any`, `Complexity.polyTimeComputable_take1`, `Complexity.polyTimeComputable_const`, `Complexity.BinArith.iterate_drop_one`, `Complexity.polyTimeComputable_tail`, `Complexity.polyTimeComputable_emitIter`, `Complexity.BinArith.flatMap_normChunk`.
