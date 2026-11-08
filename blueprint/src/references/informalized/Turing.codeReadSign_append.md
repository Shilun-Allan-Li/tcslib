<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadSign_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head-Movement Decoding

**Claim.** For every head movement $s$ and bit string $x$, reading the two-bit code for $s$ followed by $x$ succeeds and returns $(s,x)$.

**Proof.** The movement has three possible values. For a left move the code is $11$, for staying still it is $00$, and for a right move it is $10$. In each case the reader's matching clause returns that movement and leaves the suffix $x$ unchanged.
