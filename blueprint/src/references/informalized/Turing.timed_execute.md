<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_execute -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a retained action

**Claim.** If a four-tape interpreter configuration is in the pending-action state carrying action bits $a$ and halting flag $h$, then the timed interpreter, started in the execute phase with those data and with clock word $b$, takes one step to the lift of the four-tape interpreter's one-step result, preserving the clock word.

**Proof.** The first four tapes of the timed lift agree with the corresponding work tapes of the original configuration, so the timed interpreter supplies exactly the same scanned work symbols to the four-tape transition function. In the execute phase its transition is the timed version of that pending action. The action-lifting identity (`timedAction_apply`) says that applying this timed action to the lifted configuration produces the lift of the original action's result, leaving the clock word unchanged. The hypothesis that the control is the pending-action state identifies the original one-step transition with precisely that action, proving the claim.

**Key facts.** `Turing.timedAction_apply`.
