<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AReach.single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Guarded Reachability

**Claim.** If $G$ holds of configuration $a$, then its one-step successor is reachable from $a$ with $G$ holding at every configuration before the endpoint.

**Proof.** Choose time $T=1$. By the definition of the run, after one step the configuration is the one-step successor of $a$. The only time $t<1$ is $t=0$, when the run is at $a$, so the required guard follows from the hypothesis.
