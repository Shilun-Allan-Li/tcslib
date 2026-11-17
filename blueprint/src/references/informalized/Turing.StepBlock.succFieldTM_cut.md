<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.succFieldTM_cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Early Completion in a Successor Field

**Claim.** While the successor-field machine scans the complete optional-state encoding of `s`, it is not in a done state at any time strictly before the encoding length.

**Proof.** Apply the intermediate-time description of the successor-field run (`succFieldTM_trace`) at the given time. At time zero the machine is still in its assumed tag state, which is not done. At any positive time strictly below the encoding length, the trace description places the machine in the unary phase. Neither the tag nor the unary phase is a done state, proving the assertion for every such time.

**Key facts.** `Turing.StepBlock.succFieldTM_trace`.
