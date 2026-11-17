<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.polyTimeComputable_mapW -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Word Mapping

**Claim.** If $g$ is polynomial-time computable, then the function that encodes the decoded input components as a pair, repeatedly updates that pair for the prescribed $|z|+2$ iterations, emits the mapped chunks, and concatenates them is polynomial-time computable.

**Proof.** The pair update `listStep` is polynomial-time computable: it retains the first decoded component and replaces the second by its second decoded component, using the polynomial-time component projections and pair encoding. The chunk function `mapChunk` tests whether the relevant decoded component is empty. In the empty case it returns the empty word; otherwise it applies $g$ to the encoded pair of the first decoded component and the next component, then encodes the result with an empty second component. The polynomial-time conditional, projections, encoding, constants, and the hypothesis on $g$ show that this chunk function is polynomial-time computable.

It remains to bound the lengths of the iterated states so that the polynomial-time iteration-and-emission result applies. At iteration zero the state length is the input length. After the first update, the state is an encoding of the first component and the second component after one projection. More generally, `iterate_listStep` shows that the first component stays fixed while the second is repeatedly projected. Each such projection does not increase length (`length_iterate_pairSndD_le`), and the decoded component lengths are bounded by the original encoded input (`length_pair_components_le`, `length_pairSndD_le`). Together with the pair-encoding length formula, these estimates give the required linear, hence polynomial, bound on every iterate. Applying the iteration-and-emission theorem to `listStep` and `mapChunk` proves the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_slot3`, `Complexity.BinArith.polyTimeComputable_pairFstD`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`, `Complexity.BinArith.polyTimeComputable_slot2`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.iterate_listStep`, `Complexity.BinArith.length_iterate_pairSndD_le`, `Complexity.length_pair_components_le`, `Complexity.length_pairSndD_le`, `Turing.length_pairEncode`, `Complexity.polyTimeComputable_emitIter`.
