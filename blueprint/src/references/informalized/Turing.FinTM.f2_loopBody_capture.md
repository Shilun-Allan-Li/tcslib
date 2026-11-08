<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBody_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Loop-Body Computation

**Claim.** Under the agreement of the host transitions with the capture transform, the host run from the captured loop-body configuration matches the capture of the loop-body run after $t$ steps, with the stated release flag and halt marker.

**Proof.** First, the loop-body run identity (`f2_loopBody_run`) identifies the configuration reached at every time $u<t$: it is the lift of the base run, with the release flag and extra-tape cell determined by whether $u=0$ and whether the base run has halted. Since the base run is live at each such $u$, these lifted configurations are not halted. Thus the loop-body computation stays active for all times before $t$. Apply the capture simulation theorem (`capture_run`): when the host transition agrees with the capture of the loop-body transition, and the simulated machine remains active before time $t$, the host run equals the capture of the loop-body run at time $t$. Finally, substitute `f2_loopBody_run` at time $t`; its description gives exactly the asserted release flag and halt marker.

**Key facts.** `Turing.FinTM.f2_loopBody_run`, `Turing.capture_run`.
