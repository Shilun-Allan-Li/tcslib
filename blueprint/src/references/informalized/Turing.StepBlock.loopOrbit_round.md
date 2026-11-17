<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean :: Turing.StepBlock.loopOrbit_round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Compiled Round Reaches Its Live Exit

**Claim.** Under the stated representation and live-state assumptions through time $r$, the compiled configuration after $r$ exit-delimited rounds is at the live exit anchor. Its next round has positive duration at most $50(|\mathrm{tableBits}(M)|+1)$, and at every strictly intermediate time its state differs from both exit anchors.

**Proof.** The live-state assumption at time zero gives a present starting state. Apply `loopOrbit_rep` to the first $r$ rounds, using the assumed liveness at every earlier time. It shows that the resulting compiled configuration represents the simulated configuration at time $r$ and lies at the anchor selected by whether that simulated configuration is live. The liveness assumption at time $r$ makes this the live exit anchor. Now apply `loopRoundTime_spec` to the simulated configuration at time $r$ and this compiled configuration. It gives a positive next-round duration bounded by $50(|\mathrm{tableBits}(M)|+1)$, and states that every strictly intermediate configuration has a present state distinct from both exit anchors. These are exactly the asserted properties.

**Key facts.** `Turing.StepBlock.loopOrbit_rep`, `Turing.StepBlock.loopRoundTime_spec`.
