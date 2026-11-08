<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_rd_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a True Input Bit

**Claim.** If the instruction at label $\ell$ reads the next input bit and the bit at position $p$ is $1$, then from any output string $o$ the program reaches $\ell_t$ in at most one step, leaves the registers and output unchanged, and advances the input position to $p+1$.

**Proof.** Fix an arbitrary prior output $o$. The one-step transition at $\ell$ uses the read instruction specified by the hypothesis. Since the input lookup at position $p$ returns $1$, this transition goes to $\ell_t$, preserves the register assignment and output, and increments the input position to $p+1$. The one-step characterization of bounded reachability (\texttt{goes\_of\_step}) packages this transition, for every $o$, as the asserted reachability in at most one step.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
