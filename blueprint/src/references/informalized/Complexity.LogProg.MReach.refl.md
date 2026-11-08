<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MReach.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-step reachability

**Claim.** For any configuration $a$, the machine reaches $a$ from itself in zero steps, with the invariant condition required at every configuration strictly before the endpoint.

**Proof.** Choose time $0$. A run iterated zero times leaves $a$ unchanged, so the endpoint is $a$. There are no natural times strictly less than $0$, and therefore the invariant condition has no instances to check.
