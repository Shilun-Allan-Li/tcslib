<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.layerGate_args_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layer Gate Arguments Precede Their Layer

**Claim.** If $m$ is below the depth of $F$ and $u$ is a node in the successor of layer $m$, every argument vertex of its associated gate has index less than $n$ plus the cumulative number of nodes in the successor layers preceding layer $m$.

**Proof.** Unfold the definition of the gate associated with $u$ and consider its three possible shapes. For a wire, the argument list is a singleton containing the index assigned to its source node; for a negation, it is likewise a singleton. In either case the required bound follows from the upper bound on indices assigned to layer vertices (`layerVertex_lt`). For a conjunction, each argument in the deduplicated list comes from mapping the layer-vertex assignment over the original input list. Thus it is the index of some input node, and the same upper bound applies.

**Key facts.** `BoolCircuit.LayeredCircuit.layerVertex_lt`.
