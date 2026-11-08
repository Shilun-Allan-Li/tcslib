<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.reach_of_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability under endpoint equality

**Claim.** If $b$ is reachable from $a$ by a finite run whose configurations before the endpoint satisfy $G$, then any configuration $b'$ equal to $b$ is reachable from $a$ with the same property.

**Proof.** By reachability, there is a run length $T$ such that the run from $a$ reaches $b$ at time $T$, and every configuration at a time $t<T$ satisfies $G$. Since $b=b'$, the same run reaches $b'$ at time $T$. The intermediate configurations and their property $G$ are unchanged, so this witnesses the required reachability.
