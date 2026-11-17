<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.anyTrue_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Time bound for marker existence

**Claim.** For every Boolean input word $x$, the marker-existence scanner computes the one-bit word whose bit is true exactly when $x$ contains a true bit, within $|x|+1$ steps.

**Proof.** Fix $x$. The run lemma applied with empty prefix and remainder $x$ gives a time $t\le |x|+1$ at which the scanner, from its initial scanning configuration, has halted and output $[x.any\ id]$. This scanning configuration is exactly the machine's initial configuration: both have the initial state, head position, empty output, and (since there are no work tapes) identical remaining data, by extensionality for zero-tape configurations (`Cfg.ext_zero_tapes`). The equivalence between computation within time $t$ and being halted with the specified output at time $t$ (`computesInTime_iff`) therefore gives the computation claim at time $t$. Finally, the monotonicity of the time bound (`ComputesInTime.mono`) extends it from $t$ to $|x|+1$.

**Key facts.** `Turing.FinTM.anyTrue_run`, `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.mono`.
