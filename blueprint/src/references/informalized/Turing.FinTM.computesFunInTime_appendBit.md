<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_appendBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending One Bit in Linear Time

**Claim.** For each Boolean value $b$, a finite Turing machine can append $b$ to every Boolean word $x$ in time $c(|x|+1)$ for some constant $c$.

**Proof.** Choose the machine that scans the input while emitting its bits and then emits $b$, with time constant $c=1$. For an input $x$, the run description says that after $|x|$ steps the machine is in the scanning configuration with the prefix already emitted. One further step is the final transition: the scan configuration reads the symbol at the current position, and at the end of the input this is the end marker, so the machine emits $b$ and halts. Thus at time $|x|+1$ it has halted with output $x$ followed by $b$. The characterization of computation in time by halting and having the specified output ( `computesInTime_iff`) gives the required computation; the chosen time is exactly $1\cdot(|x|+1)$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.emitterAppend_run`, `Turing.FinTM.scanCfg_read`.
