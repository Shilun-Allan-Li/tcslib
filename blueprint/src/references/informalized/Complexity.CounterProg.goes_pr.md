<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_pr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Register Printing

**Claim.** If the instruction at $\ell$ prints register $r$ in unary and continues at $\ell'$, then from any output $o$ the program reaches $\ell'$ in at most one step, leaving registers and input position unchanged and appending $\rho(r)$ copies of $1$.

**Proof.** Fix an initial output $o$. The instruction prints the register value in unary, so its single transition appends a list of $\rho(r)$ true bits and moves to $\ell'$, without changing the registers or input position. The one-step transition principle (`Complexity.CounterProg.goes_of_step`) gives the desired bound.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
