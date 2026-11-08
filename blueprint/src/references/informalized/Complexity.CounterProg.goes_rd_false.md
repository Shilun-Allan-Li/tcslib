<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_rd_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Zero from Input

**Claim.** If the instruction at $\ell$ reads the next input symbol and the symbol at position $p$ is $0$, then from any output $o$ the program reaches $\ell_f$ within one step, preserving registers and output and advancing the input position to $p+1$.

**Proof.** Fix an initial output $o$. The read instruction sees the false bit at position $p$ and follows its false branch to $\ell_f$. It leaves the registers and output unchanged and advances the input position by one. The one-step transition principle (`Complexity.CounterProg.goes_of_step`) gives the claimed run bound.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
