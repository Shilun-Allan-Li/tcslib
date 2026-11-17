<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.dpStep_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step dynamic-programming update

**Claim.** Applying the encoded update to the context for $x,s,V$ and the vector of depth-$t$ values produces that same context paired with the vector of depth-$(t+1)$ values.

**Proof.** First, the pairing projections recover the context and the value vector, and the map-update identity converts the update into an encoded list whose entries are the row computations for each index below $V$ (`mapW_pairEncode`). Decoding the encoded value vector recovers its entries (`decWords_encWords`). For each index $a$, the row computation pairs the current context data with the encoded lists of candidate codes and values; the zip-update identity turns this into a list of transition-entry computations (`zipWithW_pairEncode`). Decoding the encoded lists and pairing projections identifies the entry at candidate code $a'$ with the sum of two contributions, one for each choice bit (`entryW_eq`): each contributes the current value at $a'$ exactly when the corresponding transition relation holds, and otherwise contributes zero. Summing these entries over $a'<V$ therefore gives the defining depth-$(t+1)$ dynamic-programming value at $a$. The binary-value identity ensures the decoded binary representation represents this sum, while `sumW_encWords` packages the list of such sums as the encoded next vector. The resulting pair has the original context and precisely the depth-$(t+1)$ vector.

**Key facts.** `Complexity.BinArith.pairFstD_pairEncode`, `Complexity.BinArith.pairSndD_pairEncode`, `Complexity.BinArith.mapW_pairEncode`, `Complexity.BinArith.decWords_encWords`, `Complexity.BinArith.zipWithW_pairEncode`, `Randomized.BPLInP.entryW_eq`, `Randomized.BPLInP.map_bits`, `Randomized.BPLInP.sumW_encWords`, `Randomized.BPLInP.sum_map_range`.
