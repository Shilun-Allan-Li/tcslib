<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.poolMem_pool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialized Pool Values

**Claim.** For every $n\le N$, after initialization the value at pool address $c_{\mathrm{Pool}}(n)$ is the word encoding of $n$.

**Proof.** The straight-line initialization first establishes that the one register contains the encoding of $1$ (`effects_headStraight_consts`). Starting from any memory with that one-register value, the pool initialization establishes that every pool address $c_{\mathrm{Pool}}(n)$ for $n\le N$ contains the encoding of $n$ (`effects_poolCode`). Apply this fact to the memory after straight-line initialization; by definition, the combined initialization is precisely the pool code applied to that memory.

**Key facts.** `Light.Compiler.effects_headStraight_consts`, `Light.Compiler.effects_poolCode`.
