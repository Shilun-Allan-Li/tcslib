<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.fin_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability from Equal Register States

**Claim.** If two register states are equal, there is guarded reachability from the configuration with the first state's registers to the configuration with the second state's registers at the same label.

**Proof.** Equality of the states gives equality of their register vectors, so the two configurations coincide. Reflexivity of guarded reachability supplies a zero-length run from a configuration to itself (`Complexity.LogProg.AReach.refl`); substituting the state equality identifies its endpoint with the stated configuration.

**Key facts.** `Complexity.LogProg.AReach.refl`.
