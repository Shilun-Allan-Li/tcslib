<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.exists_isStrict_fanoutTwo_of_strict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded fanout for strict circuits

**Claim.** Every strict circuit can be replaced by an equivalent strict circuit in which every vertex other than the output has positive fanout and every vertex has fanout at most two, with size at most $20$ times the original size.

**Proof.** Apply the fanout reduction construction to $C$, obtaining an intermediate circuit $D$. The construction preserves the computed function, keeps all gates strict, bounds every vertex's fanout by two, and gives $D.size\le n+5m$, where $m$ is the number of gates of $C$. Its output has fanout zero. Seal $D$ to obtain the desired circuit: sealing preserves evaluation, ensures strictness and positive fanout at every nonoutput vertex, and retains the fanout bound because the output of $D$ has fanout at most one. Sealing increases size to at most $4D.size$. Thus the final size is at most $4n+20m\le20(n+m)=20C.size$.

**Key facts.** `BoolCircuit.DAGCircuit.fanoutTwoNN_strict`, `BoolCircuit.DAGCircuit.fanoutTwoNN_hasFanoutTwo`, `BoolCircuit.DAGCircuit.fanoutTwoNN_fanout_output`, `BoolCircuit.DAGCircuit.seal_isStrict`, `BoolCircuit.DAGCircuit.seal_hasFanoutTwo`, `BoolCircuit.DAGCircuit.seal_eval`, `BoolCircuit.DAGCircuit.seal_size_le`, `BoolCircuit.DAGCircuit.fanoutTwoNN_size_le`.
