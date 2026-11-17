<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.mapW_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapping Over Encoded Words

**Claim.** For a function $g$ on bit strings and bit strings $q,w$, mapping over the encoding of $(q,w)$ produces the concatenated encodings of $g$ applied to the encodings of each word decoded from $w$, with empty second component.

**Proof.** Expand the definition of the map operation as a bounded concatenation of successive chunks. After $i$ iterations, the list state is the encoding of $q$ together with the result of decoding the second component $i$ times (`Complexity.BinArith.iterate_listStep`). Decoding either component of an encoded pair returns that component (`Complexity.pairFstD_pairEncode` and `Complexity.pairSndD_pairEncode`). Consequently, each nonempty iteration contributes the encoding of $g$ applied to the encoding of $q$ paired with the next decoded word, with empty second component. The list-loop identity (`Complexity.BinArith.flatMap_listLoop`) identifies the bounded concatenation of these contributions with the map of the decoder's output list. The chosen bound is sufficient because the encoded list has length at most that bound: the pair-encoding length formula (`Turing.length_pairEncode`) gives this after a direct length calculation. Finally, flattening the map and rewriting by the definition of `encWords` gives the stated concatenation.

**Key facts.** `Complexity.BinArith.iterate_listStep`, `Complexity.pairSndD_pairEncode`, `Complexity.pairFstD_pairEncode`, `Complexity.BinArith.flatMap_listLoop`, `Turing.length_pairEncode`.
