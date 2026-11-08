<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_release -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Release the first anchor

**Claim.** One step from the startup call on the halted body configuration, with release clear and the stop flag false, produces the non-startup call on the same configuration with state set to the anchor, release set, and no stop flag, preserving the counter word and fuel configuration.

**Proof.** The startup call is represented by a captured, padded body configuration. In its startup state, the host's control transition clears the flag and changes the call marker from startup to non-startup, setting the body state to the anchor and the release bit to true. Its input-head movement is zero, so the input position is unchanged (`moveInputPos_zero`). The transition does not write on any body or fuel tape, and the counter and payload tapes are untouched; the captured configuration already has the stated counter word and fuel contents. Thus the state, tapes, head positions, input position, and output agree with those of the specified non-startup call.

**Key facts.** `Turing.moveInputPos_zero`.
