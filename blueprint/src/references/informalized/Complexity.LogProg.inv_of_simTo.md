<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean :: Complexity.LogProg.inv_of_simTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant Along a Finite Simulation

**Claim.** For a finite simulation from $c$ to $c'$ whose pre-endpoint configurations are call-free and have register heads between $-1$ and $W$, one can choose a run length realizing the endpoint and satisfying the invariant at every earlier configuration.

**Proof.** By the definition of finite simulation, there is a length $T$ for which the run from $c$ reaches $c'$, and every configuration at time $t<T$ satisfies the midpoint conditions. Keep this same $T$ and endpoint equality. At each such time, apply the result that call-free configurations with register heads in the prescribed range satisfy the invariant (`Complexity.LogProg.inv_of_mid`). This gives the required invariant throughout the run before its endpoint.

**Key facts.** `Complexity.LogProg.inv_of_mid`.
