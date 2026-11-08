<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.slotsLe_guardLoop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Slot Length Bounds

**Claim.** A guarded loop step preserves the upper bound $L$ on the lengths of the four decoded slots.

**Proof.** Write the four slot-length bounds for $W$ as $h_1,h_2,h_3,h_4$. The loop case analysis (Complexity.BinArith.guardLoop_cases) gives either the terminal string or the encoded update. In the terminal case, the slots are empty, so all four bounds hold. In the update case, decoding the pair encodings shows that the first slot remains the old first slot, the second slot is the old second slot with its first bit dropped, the third slot is unchanged, and the fourth slot is the guarded output. Thus the first and third bounds follow from $h_1$ and $h_3$; dropping a bit cannot increase the second slot's length, so its bound follows from $h_2$. If the guard accepts the output of $g$, its length is at most that of the current first slot, which is bounded by $h_3$; if the guard rejects it, the fourth slot stays as before and is bounded by $h_4$. The pair-encoding decoding identities justify these slot identifications (Complexity.pairFstD_pairEncode and Complexity.pairSndD_pairEncode).

**Key facts.** `Complexity.BinArith.guardLoop_cases`, `Complexity.pairFstD_nil`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
