<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Configuration.lean :: Turing.inputSymbolInner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading an Interior Input Symbol

**Claim.** If the input-head position is $1+p$ and $p$ is less than the input length, then the head reads the input symbol at index $p$.

**Proof.** The position $1+p$ is neither the left-end position $0$ nor the right-end position $|input|+1$: the first exclusion follows from $p\ge 0$, and the second follows from $p<|input|$. Therefore the input-symbol definition selects the input entry at index one less than the head position. Since $(1+p)-1=p$, this is exactly the symbol at index $p$.
