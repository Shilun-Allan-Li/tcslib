<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_clean_restore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Restoration Bound

**Claim.** If the original machine remains live for the first $t$ steps, then the clean wrapper reaches, within $2t+1$ steps from the captured restoration checkpoint for the time-$t$ configuration and its recorded history, the administrative configuration with the original source work fields restored, the time-$t$ output retained, the restoration-phase control, input head at $p$, capture head at the output length, and empty output.

**Proof.** The undo-machine run lemma (`enumCont_undo_run`) says that, under the assumption that the original machine does not halt before time $t$, the undo machine starting from the logged time-$t$ configuration reaches its restoration result after exactly $2t+1$ steps. Apply the first-halt principle (`enumCont_first_halt`) to this run at time $2t+1$. It supplies a time $r\le 2t+1$ at which the undo machine is halted, with no earlier halt, and its configuration at time $r$ equals its configuration at time $2t+1$. The clean wrapper simulates the undo machine while capturing its output and returning from each simulated step through the prescribed state embedding; the simulation identity (`Turing.capture_run`) therefore identifies the wrapper's run at time $r$ with the captured undo-machine configuration at time $r$. Replacing that configuration by the undo result and using the restoration-result identity built into the final equality gives exactly the stated administrative configuration: the source fields have been restored, the retained word is the original time-$t$ output, the capture head is at its length, and the wrapper has empty physical output. The bound on $r$ is inherited from the first-halt principle.

**Key facts.** `Complexity.enumCont_undo_run`, `Complexity.enumCont_first_halt`, `Turing.capture_run`.
