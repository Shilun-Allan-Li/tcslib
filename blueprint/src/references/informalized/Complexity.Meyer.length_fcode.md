<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.length_fcode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the encoded word

**Claim.** For every Boolean word $w$, replacing each bit $b$ with the pair $(b,1)$ produces a word of length $2|w|$.

**Proof.** Induct on the word. The empty word encodes to the empty word, giving the result. For a word with first bit $b$ and tail $w'$, the encoding contributes the two-bit pair $(b,1)$ followed by the encoding of $w'$. Its length is therefore $2+2|w'|$ by the induction hypothesis, which equals twice the length of the original word.
