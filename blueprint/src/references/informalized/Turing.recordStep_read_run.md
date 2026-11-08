<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_read_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Boolean Digit Read

**Claim.** From the initial state, the digit-reading machine takes one step to a configuration identical to the starting configuration except that its state records the optional Boolean decoded from the input symbol under the head. At every time before that step, its state does not record a Boolean value.

**Proof.** In the initial state, the machine's transition is an input-only move with displacement zero and successor state equal to the optional Boolean obtained by decoding the current input symbol. The transition rule for an input-only move therefore gives the claimed updated configuration; a zero displacement leaves the input head in place (`step_of_inputMoveAction`, `moveInputPos_zero`). For the only time $u<1$, namely $u=0$, the run is still the initial configuration, whose state is `some none`, so it cannot be a state of the form `some (some b)`.

**Key facts.** `Turing.step_of_inputMoveAction`, `Turing.moveInputPos_zero`.
