<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.capture_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capture Transform Commutes with Applying an Action

**Claim.** Applying the capture transform of an action to the capture image of a configuration gives the capture image of the configuration obtained by applying the original action.

**Proof.** Compare the two configurations component by component. Their states agree because both encode the successor state through the state map, using the return state when the successor is absent; their input-head positions agree because the input movement is unchanged. On each of the original $k$ tapes, the same write and head movement are applied, so both tape contents and head positions agree. On the additional tape, if the action outputs a bit, the transformed action writes it at the current end of the stored prefix and output, then advances the head; the tape is therefore the buffer for the prefix followed by the updated output. This is the append-update identity for the buffer (`Turing.FinTM.bufferTape_append`). If there is no output bit, the additional tape and its head do not change, again matching the capture image. Finally, the transformed action emits no output directly, and the captured configuration retains the fixed external output word. Thus all components agree.

**Key facts.** `Turing.FinTM.bufferTape_append`.
