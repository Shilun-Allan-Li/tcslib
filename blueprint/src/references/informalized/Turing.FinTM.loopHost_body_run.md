<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_body_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a Live Body Run

**Claim.** If the extended body run has not halted at any time before $t$, then the loop host run for $t$ steps from its image equals the image of the extended body run at time $t$, with the chosen modes and prefix.

**Proof.** Split on the forwarding mode. In capture mode, the host's transition on a body state agrees with the extended body source's transition followed by output capture. The general capture-run theorem (`capture_run`), under the given live-prefix hypothesis, therefore identifies the host run with the captured source run at time $t$. In forwarding mode, first pad the source with one unused blank tape. The left-padding run theorem (`leftCfg_run`) shows that this padded machine follows the source run with that tape unchanged. The host transition agrees with emitting the padded transition into the host state, and the corresponding emitted configuration is exactly the forward image (`hcfg`). The emitted-run theorem (`emit_run`) now identifies the host run with the emitted padded run. Its live-prefix requirement follows from the hypothesis and the padding identity. Thus in either mode the host configuration is the image of the source configuration at time $t$.

**Key facts.** `Turing.capture_run`, `Turing.FinTM.leftCfg_run`, `Turing.emit_run`.
