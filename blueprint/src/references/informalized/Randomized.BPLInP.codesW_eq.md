<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.codesW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Word of Successive Binary Codes

**Claim.** The code-iteration word is the concatenation, in order, of the binary expansions of the natural numbers $j$ with $0\le j<B(|x|+1)^e$.

**Proof.** Let $i=B(|x|+1)^e$. The iteration formula (`Randomized.BPLInP.iterate_codeStep`) says that after $i$ steps the encoded pair has first component the binary expansion of $i$ and second component the encoded list of binary expansions of the numbers in the range from $0$ through $i-1$. Taking the second component gives the claimed word; the pair decoder recovers that component from an encoded pair (`Complexity.pairSndD_pairEncode`).

**Key facts.** `Randomized.BPLInP.iterate_codeStep`, `Complexity.pairSndD_pairEncode`.
