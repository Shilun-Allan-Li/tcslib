<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.bufferTape_pred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape contents at a predecessor index

**Claim.** For a Boolean word $w$ and a natural number $j<|w|$, the tape storing $w$ starting at cell zero contains $w_j$ at the integer cell $(j+1)-1$.

**Proof.** The integer cell $(j+1)-1$ is equal to $j$. Thus the tape value there is the value at natural-number cell $j$, which is the optional list lookup $w[j]?` by `bufferTape_nat`. Because $j<|w|$, that lookup is the symbol $w_j$ rather than `none`.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
