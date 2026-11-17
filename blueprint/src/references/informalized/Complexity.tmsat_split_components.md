<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_split_components -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Components of a Valid Odd Split

**Claim.** If the odd split of a bit string parses as a pair encoding, its total first and second projections concatenate to the original string, and the second projection is one bit longer than the first.

**Proof.** Split according to whether the odd-split search found a cut. If it found none, the split is the empty word, which does not parse as a pair encoding; this contradicts the hypothesis. Thus the search returns some cut position $i$. By `tmsat_split_some`, the position satisfies $i+(i+1)=|z|$. The split is the pair encoding of the prefix of length $i$ and the suffix after that prefix. The identity `pairDecode_pairEncode` shows that the total projections recover exactly those two pieces. The prefix and suffix partition the original string, so their concatenation is $z$. Their lengths are $i$ and $|z|-i=i+1$, giving the asserted length relation.

**Key facts.** `Complexity.tmsat_split_some`, `Turing.pairDecode_pairEncode`.
