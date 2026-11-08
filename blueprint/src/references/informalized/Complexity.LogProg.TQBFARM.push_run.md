<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.push_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pushing a value onto the stack

**Claim.** From a push state with depth $k$, stack value $S$, and pointer $p$, the machine reaches the node state with depth $k+1$, stack value $2S+b$, pointer zero, and scratch registers zero, while satisfying the guard throughout.

**Proof.** The push instruction first clears the pointer. The assumptions give the required initial register bounds. The doubling-loop result (`Complexity.LogProg.TQBFARM.dm_run`) then transfers twice the stack value into scratch register $T$ and clears $S$, reaching the move loop; its bound condition is $2S\le B$. Apply the transfer result (`Complexity.LogProg.TQBFARM.mv_run`) with source $T$ and destination $S$. It restores $S=2S$ and clears $T$. If $b$ is false, the program proceeds directly to the node state. If $b$ is true, it increments $S$ once and then increments the depth once. These final instructions produce stack value $2S+b$ and depth $k+1$; the hypotheses $2S+1\le B$ and $k+1\le B$ keep both within the bound. The pointer and other scratch registers are zero at the endpoint. The guarded runs are concatenated using `Complexity.LogProg.AReach.trans`; `cont` aligns equal register records, and `step_of` and `fin_of` account for the single instructions and unchanged endpoint.

**Key facts.** `Complexity.LogProg.TQBFARM.stp_bd`, `Complexity.LogProg.TQBFARM.step_of`, `Complexity.LogProg.TQBFARM.cont`, `Complexity.LogProg.TQBFARM.dm_run`, `Complexity.LogProg.TQBFARM.mv_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.TQBFARM.fin_of`.
