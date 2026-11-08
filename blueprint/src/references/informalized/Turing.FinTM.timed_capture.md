<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.timed_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decider-Phase Simulation

**Claim.** During the decider phase, running the timed conditional controller for $t$ steps from the configuration corresponding to $c$ gives the configuration corresponding to the decider's configuration after $t$ steps, provided the decider has not halted earlier.

**Proof.** First extend the decider to the padded machine by adding the unused work tapes. The padded machine follows the decider on its original tapes and preserves the added tapes, so its run from the corresponding padded configuration agrees at every time with the decider's run (`leftCfg_run`). Now apply the capture simulation theorem (`capture_run`): as long as the decider remains live before time $t$, the controller's capture phase tracks each decider step, storing any emitted output on its extra tape. The padded run at time $t$ is the decider's run at time $t$, so the resulting captured configuration is exactly the stated decider-phase configuration.

**Key facts.** `Turing.FinTM.leftCfg_run`, `Turing.capture_run`.
