<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_jz_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-Register Zero Test

**Claim.** If the instruction at $\ell$ tests register $r$ and $\rho(r)\ne 0$, then from any output $o$ the program reaches $\ell_1$ in at most one step, with registers and input position unchanged and output still $o$.

**Proof.** By the one-step transition principle (`Complexity.CounterProg.goes_of_step`), it is enough to identify the result of a single step for each initial output $o$. At label $\ell$, the instruction is the stated zero test. Since $\rho(r)\ne 0$, its positive branch is selected, so the new label is $\ell_1$. A zero test changes neither registers, input position, nor output. Thus the step reaches exactly the claimed state, and the principle gives the bound of one step.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
