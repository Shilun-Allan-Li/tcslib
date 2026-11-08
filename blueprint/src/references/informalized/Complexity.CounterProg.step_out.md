<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.step_out -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Output Extension

**Claim.** There is a finite bit string $e$ such that the output after one step is the current output followed by $e$.

**Proof.** If the state is halted, one step leaves its output unchanged, so take $e$ to be the empty string. Otherwise inspect the instruction at its label. Every instruction either leaves the output alone, appends one bit, or, in the register-printing case, appends a finite string of true bits. In each case the new output is the old output concatenated with precisely that appended string, which supplies the required $e$.
