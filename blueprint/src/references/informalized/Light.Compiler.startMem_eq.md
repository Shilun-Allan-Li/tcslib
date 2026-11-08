<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.startMem_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Starting Memory Decomposition

**Claim.** For all natural numbers $F,N$ and every WordRAM memory $m$, initializing the compiler's starting memory with parameters $F,N$ gives the same memory as first applying the head and pool initialization to $m$, then applying the frame initialization with parameter $F$.

**Proof.** The starting instruction list is the concatenation of the pool code and the frame code. The effect of a concatenated list is obtained by applying the effect of its first part and then the effect of its second part (`effects_append`). By definition, applying the head initialization followed by the pool code gives `poolMem N m`. Hence the starting memory is exactly the effect of the frame code on `poolMem N m`.

**Key facts.** `WordRAM.effects_append`.
