<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean :: Complexity.Codec.foldl_adStep_flatten -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Processing full chunks of symbols

**Claim.** Processing the concatenation of equal-length full chunks one symbol at a time ends with the state obtained by applying $\delta$ successively to those chunks, at position zero, with some final buffer.

**Proof.** Induct on the list $L$ of chunks. For no chunks, processing the empty concatenation leaves the initial state and buffer unchanged, which agrees with folding $\delta$ over the empty list. For a first chunk $ch$ followed by the remaining chunks, the one-full-chunk result shows that processing $ch$ takes state $s$ to $\delta(s,ch)$ and resets the position to zero, producing some buffer. Apply the induction hypothesis to the remaining chunks starting from that state and buffer. Since the concatenation processes the first chunk and then the remainder, and the fold of $\delta$ does the same, the resulting state is $L.\mathrm{foldl}(\delta,s)$, the position is zero, and a final buffer exists.

**Key facts.** `Complexity.Codec.foldl_adStep_chunk`.
