<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_clean_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured simulation phase

**Claim.** If the source machine remains live before time $t$, then the clean wrapper simulates its first $t$ steps in the captured logged configuration, with empty captured prefix and output.

**Proof.** Use the capture-simulation theorem with the logged source machine as the simulated machine and the clean wrapper as its host. The clean wrapper's transition on an embedded source state is precisely the capture of the logged machine's transition, with the source work tapes read from the corresponding tape block. The hypothesis that the source computation is live at every time before $t$ is exactly the theorem's condition ensuring that each simulated step is performed rather than stopping at a halted source state. The capture-simulation theorem therefore identifies the host configuration at time $t$ with the capture of the logged source configuration at time $t$. Finally, the logged-run identity identifies that configuration as the source machine's time-$t$ configuration together with the history of its first $t$ steps. The captured prefix and output remain empty, as stipulated in the chosen capture setup.

**Key facts.** `Turing.capture_run`, `Complexity.enumCont_log_run`.
