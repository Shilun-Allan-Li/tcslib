<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Compiler.length_frameInit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame Initialization Length

**Claim.** For all natural numbers $F$ and $n$, the frame initialization list has length $2F$.

**Proof.** The initialization is a flat map over the $F$ indices in the range from $0$ to $F-1$. For each index it produces exactly two instructions, regardless of whether that index is below $n$. Thus the total length is $2F$.
