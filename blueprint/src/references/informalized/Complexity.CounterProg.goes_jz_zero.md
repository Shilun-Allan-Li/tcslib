<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_jz_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Register Zero Test

**Claim.** If the instruction at $\ell$ tests register $r$ and $\rho(r)=0$, then from any output $o$ the program reaches $\ell_0$ in at most one step, with registers and input position unchanged and output still $o$.

**Proof.** By the one-step transition principle (`Complexity.CounterProg.goes_of_step`), it suffices to determine the result of one step for each initial output $o$. The instruction at $\ell$ is the stated zero test, and $\rho(r)=0$, so the zero branch leads to $\ell_0$. The test leaves the register assignment, input position, and output unchanged. Hence this step has precisely the required result.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
