<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.slots_yI -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment at the final tape slot

**Claim.** At the final singleton index, the assembled function has value $y$.

**Proof.** The index $yI$ is the unique position in the final singleton block. The assembled function was defined by appending the constant singleton function with value $y$ after the first two blocks, so its value at this position is $y$.
