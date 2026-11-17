<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadOutput_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optional Output Decoding

**Claim.** For every optional bit $b$ and bit string $x$, reading the two-bit code for $b$ followed by $x$ succeeds and returns $(b,x)$.

**Proof.** There are three possibilities for the optional bit. If there is no output, its code is $00$, which the reader decodes as no output and leaves $x$. If the output is $0$ or $1$, its code is respectively $10$ or $11$, and the corresponding reader clause returns that bit and leaves $x$. Thus in each case the result is $(b,x)$.
