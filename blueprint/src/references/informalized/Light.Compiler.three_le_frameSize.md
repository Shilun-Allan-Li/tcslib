<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.three_le_frameSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound on frame size

**Claim.** For every program $P$, its frame size is at least $3$.

**Proof.** The frame size is the maximum of $3$ and another natural number. A maximum is at least either of its entries, so it is at least $3$.
