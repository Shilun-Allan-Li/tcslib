<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_mapSetup_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on setup steps

**Claim.** At every configuration not in a state representing a simulated state of $M$, the forward and non-forward mapping machines have the same one-step successor.

**Proof.** Split according to the configuration's state. If it is halting, both machines leave the configuration unchanged. If it is a simulated-state state, the assumed exclusion is contradicted, so this case cannot occur. In each remaining state—one of the parsing states or another setup state—the transition rules are independent of the mode, and hence the resulting steps agree.
