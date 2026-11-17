<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_zipStream -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Padded Interleaving

**Claim.** The function that takes the total first and second projections of a bit string, pairs their bits with zero padding for the prescribed number of positions, and concatenates the pairs is polynomial-time computable.

**Proof.** First construct one iteration that removes the first bit from each projection and re-encodes the remaining pair. This iteration is polynomial-time computable by composing the projections with the polynomial-time tail operation and then using polynomial-time pair encoding. Construct also a polynomial-time chunk function that outputs the current head of each projection, with a zero for an empty projection, by composing each projection with the head-with-default operation and concatenating the results. The component-length bound for decoded pairs, together with the length formula for pair encoding, bounds the length of every iterate by a polynomial in the input length. The polynomial-time iterated-emission theorem therefore shows that emitting these chunks for the required range of iteration indices is polynomial-time computable. Finally, identify the emitted list with the desired output: the first chunk uses the original projections, and each subsequent iterate has the two projections obtained by dropping the corresponding number of bits, as given by the iterate formula for the removal step. The padded-zip expansion says that concatenating precisely these head pairs is the same as flattening the padded pair list.

**Key facts.** `Complexity.PolyTimeComputable.tail`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.append`, `Complexity.PolyTimeComputable.headD`, `Complexity.length_pair_components_le`, `Turing.length_pairEncode`, `Complexity.BinArith.iterate_zipStep`, `Complexity.polyTimeComputable_emitIter`, `Complexity.BinArith.flatMap_zipChunk`.
