<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_timed_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Run Before Halting

**Claim.** If the run of $D$ from $c$ is live at every step before $t$, then the timed conditional machine run for $t$ steps from the control configuration associated with $c$ equals the control configuration associated with $D$'s configuration after $t$ steps.

**Proof.** Pad $D$ with the unused work tapes reserved for the two branches. The padded machine follows $D$ exactly while preserving those extra tapes: the left-tape simulation identity (`leftCfg_run`) identifies its run from the padded configuration with the padded configuration of $D$'s run at every time. Apply the capture-run theorem (`capture_run`) to this padded simulation. Its liveness hypothesis follows from the assumed liveness of $D$: by the same run identity, the simulated configuration at each $s<t$ has the state of $D$'s configuration at $s$, so it is not halted. The capture theorem therefore says that after $t$ steps the host is the captured padded configuration of the padded run. Using the run identity once more at time $t$ gives precisely the stated control configuration.

**Key facts.** `Turing.FinTM.leftCfg_run`, `Turing.capture_run`.
