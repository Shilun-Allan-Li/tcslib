<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejecting an undecodable input

**Claim.** When $x$ has no valid paired decoding, the forward simulator reaches a halted configuration with empty output within the stated bound, and its run agrees with the non-forward simulator at every time.

**Proof.** The setup result (`a2_map_setup`) supplies a time $u$ within the bound at which the non-forward simulator is halted with empty output, since decoding is undefined. First show that the non-forward run never enters a run state. If it did so by time $u$, stationarity after entry (`a2_mapSetup_stationary`) would make its configuration at that time equal to its halted configuration at $u$, a contradiction. If it entered after $u$, the halted-run property (`runFrom_of_halt`) would instead make that later configuration equal to the halted configuration at $u$, also a contradiction. Thus entry never occurs. The prefix-agreement result (`a2_mapSetup_run`) now applies at every time, because its hypothesis only requires absence of entry at earlier times. Hence the forward and non-forward runs agree for all times; in particular, at $u$ the forward run is halted and has empty output, as required.

**Key facts.** `Turing.FinTM.a2_map_setup`, `Turing.FinTM.a2_mapSetup_stationary`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.FinTM.a2_mapSetup_run`.
