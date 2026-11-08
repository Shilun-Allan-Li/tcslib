<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_goto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run rule for a goto instruction

**Claim.** If the instruction at $\ell$ jumps to $\ell'$, then from any output string $o$ the program reaches $\ell'$ within at most one step, with the same registers, input position, and output.

**Proof.** Fix an output string $o$. The instruction hypothesis makes the next transition a goto: it changes the label to $\ell'$ and leaves the registers, input position, and output unchanged. Applying the one-step run principle (`goes_of_step`) gives the asserted run bound and final state.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
