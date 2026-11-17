<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run rule for a halt instruction

**Claim.** If the instruction at $\ell$ is halt, then from any output string $o$ the program reaches its halted state within at most one step, with the same registers, input position, and output.

**Proof.** Fix an output string $o$. Executing the halt instruction changes the label to the halted state and leaves the registers, input position, and output unchanged. The one-step run principle (`goes_of_step`) yields the claimed run in at most one step.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
