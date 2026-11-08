<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MReach.of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Changing the reachability endpoint

**Claim.** If the machine reaches $b$ from $a$ with invariant $G$ before the endpoint and $b=b'$, then it reaches $b'$ from $a$ with the same invariant condition.

**Proof.** Equality allows the endpoint of the witnessed reachability statement to be replaced by the equal configuration $b'$. The witnessing time and all conditions on the run remain unchanged.
