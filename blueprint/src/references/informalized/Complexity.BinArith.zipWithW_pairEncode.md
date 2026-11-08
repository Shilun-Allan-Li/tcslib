<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.zipWithW_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zip Over Encoded Word Lists

**Claim.** For any $g,q,l_1,l_2$ as stated, applying $zipWithW$ to the nested pair encoding yields the concatenation of the empty-second-component encodings of $g(\langle q,x,y\rangle)$ over the termwise decoded pairs from $l_1$ and $l_2$, stopping when either decoded list ends.

**Proof.** Unfold the definition of $zipWithW$ and consider its successive states, obtained by iterating the step map $zipStep$. The iterate formula shows that after each step the state is the pair encoding of the remaining tails of the two component strings. Pair decoding a pair encoding recovers its two components ($pairFstD_pairEncode$ and $pairSndD_pairEncode$), so each emission is empty as soon as either remaining decoded list is empty; otherwise it is the encoding with empty second component of $g$ applied to the nested encoding of $q$ and the two current decoded words. The finite-loop identity for $flatMap_zipLoop$ identifies the concatenation of these emissions with the flattened zipped list. Its range bound is satisfied because the encoding length formula gives enough iterations to cover the first input list. Finally, the definition of $encWords$ and the list identity for flattening a zipped map give the claimed encoding of the outputs.

**Key facts.** `Complexity.BinArith.iterate_zipStep`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Turing.length_pairEncode`, `Complexity.BinArith.flatMap_zipLoop`.
