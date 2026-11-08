<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_right_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right-Boundary Normalization Bound

**Claim.** If $M$ computes output $o$ from $x$ in exactly $T$ steps, then its right-boundary wrapper computes $o$ after exactly $T+|x|+2$ steps and has input head at position $|x|+1$.

**Proof.** The computation hypothesis says the source run is halted at time $T$ and has output $o$ (`Turing.FinTM.computesInTime_iff`). The endpoint theorem identifies the wrapper's configuration after $T+|x|+2$ steps with the scan configuration built from that halted source run (`Turing.FinTM.emCall_right_endpoint`). By the definition of that scan configuration, its administrative state is halted and its input-head position is $|x|+1$. Its output is the source run's output, namely $o$. The characterization of computation in a specified time by halting and output now proves the wrapper computes $o$ at that time (`Turing.FinTM.computesInTime_iff`).

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.emCall_right_endpoint`.
