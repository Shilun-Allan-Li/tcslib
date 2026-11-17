<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_lookup_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepare Registers for Lookup

**Claim.** Under the four stated inequalities, the machine reaches the search state with the specified prepared register values, maintaining safety and the register bound along the way.

**Proof.** The initial register vector satisfies the required bound by the componentwise register-vector estimate (`Complexity.dropValues_bound`). The copy-stage lemma then shows that the machine copies the designated register into the target register and reaches the next state with the updated vector (`Complexity.drop_copy_run`). From that state, one machine step enters the search state and leaves the registers unchanged; its safety condition follows from the general safety property for machine configurations (`Complexity.drop_preS`), and the unchanged vector remains bounded. The reflexive reachability fact closes the zero-step remainder (`Complexity.LogProg.AReach.refl`), while the one-step reachability rule incorporates the step (`Complexity.LogProg.AReach.step`).

**Key facts.** `Complexity.dropValues_bound`, `Complexity.drop_copy_run`, `Complexity.drop_preS`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.step`.
