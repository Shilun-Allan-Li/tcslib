<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.mv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register transfer loop

**Claim.** The transfer loop moves the contents of $T$ into $S$, clears $T$, and reaches the control label determined by $b$, while respecting the register bound and program precondition throughout.

**Proof.** Apply the general move-loop result (`Complexity.LogProg.move_run`) with source register $T$ and destination register $S$. Its three instruction phases test whether $T$ is zero, decrement $T$, and increment $S$, repeating until the source is exhausted. The registers are distinct, and the program’s phases have exactly these instructions. The register bound follows from the initial bounds together with $S+T\le B$: during each transfer the sum of $S$ and $T$ is preserved, so neither register exceeds $B$; the other registers remain unchanged. The loop therefore ends with $T=0$ and $S$ equal to its initial value plus the initial contents of $T$. The final control label is the exit chosen by $b$, as asserted.

**Key facts.** `Complexity.LogProg.move_run`, `Complexity.LogProg.TQBFARM.St.Bd.toV`.
