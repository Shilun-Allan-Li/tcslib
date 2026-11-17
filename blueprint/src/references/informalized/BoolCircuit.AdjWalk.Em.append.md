<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.Em.append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Emitted Segments

**Claim.** If a configuration emits segment $S$ from position $k$ with postcondition $P$, and every suitable postcondition-$P$ configuration emits $T$ from the next position with postcondition $Q$, then it emits the concatenation $ST$ from $k$ with postcondition $Q$.

**Proof.** We verify the two parts of the emission property. First suppose the queried position $i$ lies within the concatenated segment. If $i<k+|S|$, it lies within $S$, so the first emission property gives the required halt and the bit of $ST$ there is the bit of $S$. Otherwise, the first property supplies a configuration satisfying $P$ reachable after emitting $S$. The continuation hypothesis applies there, since the position is at or beyond the end of $S$ and still inside $ST$. It gives the halt for the corresponding position in $T$; the reached configuration can be prepended to this halting run by the reach-to-halt principle (`AReach.halt`). The offset into $T$ is $i-(k+|S|)$, equal to the offset obtained by subtracting $|S|$ from $i-k$. Second, if $i$ is at or beyond the end of $ST$, the first property reaches a configuration satisfying $P$, and the continuation property then reaches one satisfying $Q$. Composing these reaches gives the required reach for the concatenation (`AReach.trans`).

**Key facts.** `Complexity.LogProg.AReach.halt`, `Complexity.LogProg.AReach.trans`.
