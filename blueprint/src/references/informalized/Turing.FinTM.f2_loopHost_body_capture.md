<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_body_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capture of a live body run

**Claim.** If the body-source run is live at every time before $t$, then after $t$ steps the host started with the capture of $c$ is exactly the capture of the body-source configuration reached at time $t$.

**Proof.** The host transition on an embedded body state agrees with the capture of the body-source transition, as required by the capture simulation theorem (`capture_run`). The assumed liveness at every earlier time is precisely its condition preventing the host from leaving the embedded body run for its return state. Applying that theorem gives the claimed equality of configurations at time $t$.

**Key facts.** `Turing.capture_run`.
