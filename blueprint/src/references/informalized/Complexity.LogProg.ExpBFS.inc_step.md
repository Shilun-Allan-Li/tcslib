<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.inc_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Before an Increment

**Claim.** If the instruction at $l$ increments register $r$ and continues at $l'$, then any invariant-respecting reachable configuration from $l'$ with $r$ increased by one is also invariant-respectingly reachable from $l$ with the original state, memory, and head.

**Proof.** Apply the general one-step reachability principle for deterministic register instructions (`Complexity.LogProg.ExpBFS.step_of`) to the instruction at $l$. Its register update is precisely the state with register vector `Function.update` at $r$ by the old value plus one, so the hypothesis supplies the continuation reachability from the post-increment configuration. The assumed bounds on the original state and head provide the bounds required by that principle. It therefore prepends the increment step and yields the claimed reachability from the original configuration.

**Key facts.** `Complexity.LogProg.ExpBFS.step_of`.
