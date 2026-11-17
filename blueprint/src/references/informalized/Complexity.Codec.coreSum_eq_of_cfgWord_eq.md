<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.coreSum_eq_of_cfgWord_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of the Configuration Core

**Claim.** If two configurations are in the window of radius $s$ and have equal configuration words, then their cores and output summaries are equal.

**Proof.** The configuration words consist of a fixed-length sequence of cell chunks followed by the padded input-head position and a terminator. The chunk sequences have equal lengths (`length_chunksWord`), so equality of the full words gives equality of the chunk portions and of the remaining suffix. Applying the binary-value map to the equal padded suffixes recovers equality of the input-head positions (`bitsVal_padBits`). Equality of the chunk portions gives equality of corresponding cell values (`chunksWord_inj`). At cell zero, this identifies the state and the output summary; injectivity of the summary index then identifies the summaries themselves (`sumIdx_injective`). For any tape coordinate $z$ with $|z|\le s$, use the cell indexed by $(z+s)$ to recover the tape symbol and whether the head is at $z$. The window bound ensures this index lies among the encoded cells, and its represented coordinate is exactly $z$. Hence the two tape contents agree throughout the window, and the head-position predicates agree there. Outside the window both tapes are blank by the hypotheses, so the full tape functions agree. Finally, each head position lies inside the window, and the already recovered head-position predicates therefore give equality of the work-tape head positions. Together with equality of the input position, state, and output summary, this proves equality of the core summaries.

**Key facts.** `Complexity.Codec.length_chunksWord`, `Complexity.Codec.bitsVal_padBits`, `Complexity.Codec.chunksWord_inj`, `Complexity.Codec.sumIdx_injective`.
