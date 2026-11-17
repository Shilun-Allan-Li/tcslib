<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_dec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step decrement behavior

**Claim.** If the instruction at $\ell$ decrements register $r$ and continues at $\ell'$, then from any output string $o$ the program reaches $\ell'$ within at most one step, with register $r$ decreased by one with zero truncated at zero, all other registers unchanged, the same input position, and output still $o$.

**Proof.** Fix an output string $o$. By the instruction hypothesis, the single-step transition from the state with label $\ell$ executes the decrement instruction. It sets the label to $\ell'$, updates register $r$ to $\rho(r)-1$ (with natural-number subtraction, so zero remains zero), and leaves every other register, the input position, and the output unchanged. The one-step run principle (`goes_of_step`) turns this direct transition into a run of at most one step with the claimed result.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
