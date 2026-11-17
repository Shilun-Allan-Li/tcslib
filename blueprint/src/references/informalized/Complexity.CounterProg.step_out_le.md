<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.step_out_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Output Growth Bound

**Claim.** If every register in $s$ is at most $K$, then the output length after one step is at most the current output length plus $K+1$.

**Proof.** If the state is halted, the output does not change. For an active state, inspect its instruction. Instructions that do not print preserve the output length; a single-bit output instruction increases it by one. A register-printing instruction appends as many bits as the relevant register contains, at most $K$. Thus every case increases the length by at most $K+1$, proving the bound.
