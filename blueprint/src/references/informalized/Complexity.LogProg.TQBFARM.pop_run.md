<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.pop_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Returning from a recursive level

**Claim.** From depth $k+1$ and stack value $2S+b$, the machine returns to depth $k$ and stack value $S$, with pointer and scratch registers zero and the guard maintained. The final label is `rt v` when $b$ is true and the first-copy return label when $b$ is false.

**Proof.** The return begins at label `rt v`. Since the depth is $k+1>0$, the root test continues to `pop v`; the next instruction decrements the depth to $k$ and reaches `par v`. The bounds required for these steps follow from $k+1\le B$ and $2S+1\le B$, which also bounds $2S+b$. At `par v`, the program tests the parity of the stack. If $b$ is false, the stack is $2S$, so the even branch halves it to $S$ and reaches `cp (.qA v) 0`. If $b$ is true, the stack is $2S+1$, so the odd branch halves it to $S$ and returns to `rt v`. In either case the depth is $k$, the pointer and scratch registers remain zero, and every intervening configuration satisfies the guard. The register-record identifications are handled by `cont`; the unchanged final state is supplied by `fin_of`.

**Key facts.** `Complexity.LogProg.TQBFARM.stp_bd`, `Complexity.LogProg.TQBFARM.step_of`, `Complexity.LogProg.TQBFARM.cont`, `Complexity.LogProg.TQBFARM.fin_of`.
