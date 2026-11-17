<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_rd_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading at the End of Input

**Claim.** If the instruction at $\ell$ reads the next input symbol and there is no symbol at position $p$, then from any output $o$ the program reaches $\ell_e$ within one step, leaving registers, input position, and output unchanged.

**Proof.** For any initial output $o$, the read instruction finds no input symbol at position $p$, so it follows its end branch to $\ell_e$. This branch consumes no input and leaves registers and output unchanged. The one-step transition principle (`Complexity.CounterProg.goes_of_step`) gives the claimed result.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
