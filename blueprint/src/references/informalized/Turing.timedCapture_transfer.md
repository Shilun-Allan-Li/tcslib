<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCapture_transfer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer from a Halted Configuration

**Claim.** If the source configuration is halted, one capture-machine step from its embedded configuration equals the interpreter-entry configuration associated with the source.

**Proof.** In a halted source configuration, the embedded state is present as an outer capture state but contains the halted marker. Therefore the capture transition takes the branch that enters the timed interpreter's initial state and makes no tape writes, output, or head movements. The resulting state and all retained configuration fields agree with interpreter entry. In particular, the input head remains fixed because moving it by zero leaves it unchanged (`moveInputPos_zero`); the work-tape heads also remain fixed because their movements are zero.

**Key facts.** `Turing.moveInputPos_zero`.
