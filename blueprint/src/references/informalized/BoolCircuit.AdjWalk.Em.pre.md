<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.Em.pre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a Bounded Reach

**Claim.** If $a$ reaches $b$ while maintaining the register bound, and $b$ satisfies the emission property for a segment starting at $k$ with postcondition $P$, then $a$ satisfies that same emission property.

**Proof.** For the halting clause, the property at $b$ supplies a bounded run that halts with the required answer. Prepending the given bounded reach from $a$ to $b$ yields a bounded run from $a$ with the same answer (`Complexity.LogProg.AReach.halt`). For the reachability clause, the property at $b$ supplies an endpoint $c$ satisfying $P$ and a bounded reach from $b$ to $c. Keep that endpoint and concatenate the reach from $a$ to $b$ with the reach from $b$ to $c (`Complexity.LogProg.AReach.trans`). These establish the two clauses of emission from $a$.

**Key facts.** `Complexity.LogProg.AReach.halt`, `Complexity.LogProg.AReach.trans`.
