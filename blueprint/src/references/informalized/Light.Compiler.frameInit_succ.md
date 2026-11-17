<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/CallFrames.lean :: Light.Compiler.frameInit_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Frame Initialization

**Claim.** Initializing $F'+1$ cells is the code for initializing the first $F'$ cells followed by the two instructions that compute the next address and store temporary $F'$ when $F'<n$, or the zero-cell value otherwise.

**Proof.** Expand the definition of frame initialization: it maps each index in the range to its pair of instructions. The successor decomposition of the natural-number range separates its earlier indices from the final index $F'$. Mapping over that decomposition and distributing the concatenation through `flatMap` gives exactly the first $F'$ initialization instructions followed by the pair for index $F'$.
