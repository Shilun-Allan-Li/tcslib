<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.goes_stop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Immediate halt at stop

**Claim.** Starting the counter program at its stop label halts in one step, leaves the register assignment and input position unchanged, and appends no output.

**Proof.** At the stop label, the program instruction is halt. The one-step halt fact states that whenever a label carries the halt instruction, the run reaches the halted state after one step with registers and input position unchanged and no additional output (\texttt{Complexity.CounterProg.goes_halt}). Applying it to the stop label proves the claim.

**Key facts.** `Complexity.CounterProg.goes_halt`.
