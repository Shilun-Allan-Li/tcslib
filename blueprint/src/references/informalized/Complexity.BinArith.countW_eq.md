<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.countW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary count of decoded words

**Claim.** For every bit string $w$, the count defined by testing the successive second-component projections of $w$ is a unary word with one true bit for each word in the recursive decomposition of $w$.

**Proof.** The list-loop identity `flatMap_listLoop` rewrites the count as one contribution for each word in `decWords w`: the contribution associated to a decoded word is the singleton list `[true]`. Hence the result is the concatenation of exactly $(\mathrm{decWords}\,w).length$ copies of `true`, which is the stated replicate.

**Key facts.** `Complexity.BinArith.flatMap_listLoop`.
