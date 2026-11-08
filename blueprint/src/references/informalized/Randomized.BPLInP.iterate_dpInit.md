<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.iterate_dpInit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated Dynamic-Programming Initialization

**Claim.** After $i$ iterations of the dynamic-programming update, the encoding initialized from $N,c,B,e,x$ is the pairing of the context encoding for these parameters with the encoded vector of dynamic-programming values at time $i$.

**Proof.** First rewrite the initialized encoding using the initialization identity (`Randomized.BPLInP.dpInit_eq`): it is the pairing of the context with the time-zero vector. The parameter identity (`Randomized.BPLInP.ctxW_eq`) identifies this context with the context built from the stated space bound and vector size. The iterated-update formula (`Randomized.BPLInP.iterate_dpStep`) then carries that pairing, with its context fixed, from the time-zero vector to the vector at time $i$.

**Key facts.** `Randomized.BPLInP.dpInit_eq`, `Randomized.BPLInP.ctxW_eq`, `Randomized.BPLInP.iterate_dpStep`.
