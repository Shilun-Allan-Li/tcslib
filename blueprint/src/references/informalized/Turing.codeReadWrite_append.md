<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadWrite_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Write decoding after encoding

**Claim.** For every optional work-tape write $b$ and bit string $x$, the optional-write reader applied to the two-bit encoding of $b$ followed by $x$ succeeds and returns $b$ and $x$.

**Proof.** There are four possible optional-write values: no write, an explicitly empty option, a write of false, and a write of true. In each case the encoding is respectively $00$, $01$, $10$, or $11$. The reader recognizes the corresponding two-bit prefix and returns the associated value while leaving the arbitrary suffix $x$ unchanged.
