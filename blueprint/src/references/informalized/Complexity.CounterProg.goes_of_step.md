<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_of_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Run Bound

**Claim.** If every output string $o$ is carried by one step from the specified initial state to the specified target state, with $e$ appended, then the program reaches that target within one step and appends $e$.

**Proof.** Fix an initial output $o$. By hypothesis, one application of the transition function sends the state with output $o$ to the stated target state with output $o$ followed by $e$. Thus the run of length one has the required endpoint, and one is at most the allowed bound of one.
