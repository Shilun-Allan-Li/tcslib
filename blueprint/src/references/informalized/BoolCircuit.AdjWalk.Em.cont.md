<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.Em.cont -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuation of an Emission Property

**Claim.** If a configuration satisfies the emission property for segment $S$ with postcondition $P$, and every suitable configuration satisfying $P$ can reach one satisfying $Q$, then it satisfies the same emission property with postcondition $Q$.

**Proof.** The part of the emission property concerning positions inside $S$ is unchanged, so it follows directly from the original property. For the other part, the original property reaches a configuration satisfying $P$ once the entire segment has been emitted. By hypothesis, that configuration can in turn reach one satisfying $Q$. Composing the two reaches proves the required conclusion (`AReach.trans`).

**Key facts.** `Complexity.LogProg.AReach.trans`.
