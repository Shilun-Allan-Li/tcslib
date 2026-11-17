<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.synStep_matrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Syntax Scan State Identity

**Claim.** Scanning any finite Boolean list $x$ from combined syntax state $q$ ends in the combined state corresponding to scanning $x$ from $q$ with the six-state syntax transition.

**Proof.** Induct on the list. For the empty list, both scans leave their initial state unchanged. For a list whose first bit is $b$ and remaining suffix is $x$, the combined scan first takes the transition on $b$, moving to the combined state for the six-state state obtained from $q$ by that transition. Apply the induction hypothesis to the suffix with this updated state. The resulting combined state is exactly the six-state scan of the full list, embedded in the combined state space.
