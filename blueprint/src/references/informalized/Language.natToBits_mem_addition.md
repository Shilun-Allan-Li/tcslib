<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: Language.natToBits_mem_addition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Addition Encoding

**Claim.** If $m+n<2^k$, then concatenating the $k$-bit representations of $m$, $n$, and $m+n$ gives a word in the Boolean addition language.

**Proof.** Choose the three component words to be the stated $k$-bit representations. They have equal length $k$, and their concatenation is exactly the word under consideration. The binary-value identity for a bounded $k$-bit representation, $	ext{bitsVal}(	ext{natToBits}(k,r))=r$ when $r<2^k$ (BoolCircuit.bitsVal_natToBits), applies to $m$ and $n$ by the hypothesis and its consequences, and to $m+n$ by the given bound. Hence the third component has value $m+n$, equal to the sum of the values of the first two, as required.

**Key facts.** `BoolCircuit.bitsVal_natToBits`.
