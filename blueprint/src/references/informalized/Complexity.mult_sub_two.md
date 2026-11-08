<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_sub_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two Successive Decrements

**Claim.** If the program decrements register $r$ at each of two successive states, then it reaches the destination state with register $r$ reduced by two using truncated natural subtraction, all other registers unchanged, and the safety conditions maintained before arrival.

**Proof.** The initial configuration satisfies the program’s safety conditions by the state precondition lemma (`mult_preconditions`), and its registers obey the assumed bound. After the first decrement, the changed register is its former value minus one; this remains below the same bound because subtraction cannot increase a natural number. The register-update bound (`register_update_le`) preserves the bound for the whole register assignment. The one-step reachability fact (`AReach.single`) accounts for the second decrement, and composing that step with the first via `AReach.step` gives the destination configuration. The two successive truncated decrements equal subtraction by two, and the update identities leave all other registers unchanged.

**Key facts.** `Complexity.mult_preconditions`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`.
