<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_inc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run rule for incrementing a register

**Claim.** If the instruction at $\ell$ increments register $r$ and continues at $\ell'$, then from any output string $o$ the program reaches $\ell'$ within at most one step, with input position $p$, output $o$, and register assignment equal to $\rho$ except that register $r$ has value $\rho(r)+1$.

**Proof.** Fix an output string $o$. The instruction hypothesis says the next transition increments register $r$ and moves to label $\ell'$. The transition updates that register to $\rho(r)+1$, leaves all other registers unchanged, and preserves the input position and output. The one-step run principle (`goes_of_step`) gives the stated result within at most one step.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
