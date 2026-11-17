<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_lastBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Last-Bit Function

**Claim.** The function that returns the one-bit word containing the last bit of a Boolean word, using false for the empty word, is polynomial-time computable.

**Proof.** First, polynomial-time computability is closed under composition, and dropping the first bit is polynomial-time computable. Composing the latter with the polynomial-time emptiness test gives a polynomial-time test for whether the tail is empty. Thus the conditional function `lastChunk`—which returns the first bit as a one-bit word when the tail is empty and the empty word otherwise—is polynomial-time computable, using the polynomial-time operations of taking the first bit and returning a constant word, together with the polynomial-time conditional construction.

Now iterate the operation of dropping the first bit and, at each iterate, emit its `lastChunk`. The iterates have length at most the original word length, so the polynomial-time iteration-and-concatenation principle applies. The emitted chunks concatenate to `w.getLast?.toList` (`flatMap_lastChunk`), since every chunk is empty except the one corresponding to the final bit, if there is one. Finally, take the head of this list, defaulting to false. For a nonempty input the list contains exactly its last bit; for an empty input it is empty, so the default is false. Composition with the polynomial-time head-with-default function proves the claim.

**Key facts.** `Complexity.polyTimeComputable_tail`, `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_take1`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_emitIter`, `Complexity.BinArith.iterate_drop_one`, `Complexity.BinArith.flatMap_lastChunk`, `Complexity.polyTimeComputable_headD`.
