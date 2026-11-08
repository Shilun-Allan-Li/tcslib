<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_fuel_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Phase Captures the Fuel Run

**Claim.** If the relocated fuel machine does not halt before time $t$, then the loop host, started from the capture embedding of its initial configuration, follows that machine for $t$ steps and ends at the capture embedding of its time-$t$ configuration.

**Proof.** The host’s transition on an embedded fuel state agrees with the fuel machine’s transition followed by capture, as required by the capture-run theorem. The assumed nonhalting condition holds at every time strictly before $t$, so the host does not leave the embedded fuel computation during those steps. Applying the capture-run theorem with empty capture prefix and output yields the asserted equality of configurations at time $t$.

**Key facts.** `Turing.capture_run`.
