<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_apply_record -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Applying a Decoded Transition Record

**Claim.** Applying a decoded transition record in the universal interpreter produces the simulation checkpoint for the configuration obtained by applying that action to the source configuration, with the table cursor set to $p$.

**Proof.** Let the interpreter configuration be the specified record-application configuration. First, the input-reading property of the simulation encoding says that the interpreter sees the source machine's input symbol, even when its auxiliary boundary marker is present (the equality supplied by `universalInput_read`). The decoded action bits recover the action's input-head direction, work-tape write instruction and direction, and output symbol (`universalActionBits_decode`). Substituting these decoded fields into the interpreter's transition rule shows that it performs exactly the virtual input move, applies the action's work-tape update, appends the prescribed output, and enters the main control state unless the action halts. This identifies the interpreter's transition with the action needed for the simulation. The input position then agrees with the source action's moved input position by the simulation input-movement property (`universalInput_move`). Finally, compare configuration components: the first two work tapes are left unchanged, the simulated work tape receives precisely the source action's update, and the auxiliary tape is unchanged; the head positions agree by the same input-movement property and the source action's work-head movement. The state and output components are exactly those prescribed by the action. Hence the resulting configuration is the claimed simulation checkpoint.

**Key facts.** `Turing.universalInput_read`, `Turing.universalActionBits_decode`, `Turing.universalInput_move`.
