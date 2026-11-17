<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_fuel_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Simulation Under Capture

**Claim.** If the fuel-source run from $c$ is live at every time strictly before $t$, then for $t$ steps the loop-host run from the capture configuration of $c$ is exactly the capture configuration of the fuel-source run after $t$ steps.

**Proof.** The host transition on a state embedded from the fuel machine is, by its definition, the captured fuel-machine transition: it applies the fuel transition to the original tapes and uses the extra tape to record any emitted output. Thus the required transition-agreement hypothesis of the capture simulation theorem holds by unfolding the transition definitions. Since the fuel run is not halted at any time before $t$, the capture simulation theorem (`capture_run`) applies for the full duration. It identifies the host run at time $t$ with the capture configuration of the fuel run at time $t$, preserving the claimed equality exactly.

**Key facts.** `Turing.capture_run`.
