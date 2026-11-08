<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.DAGCircuit.toTree_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Unfolded Circuit

**Claim.** If the gates of $C$ have pairwise distinct input vertices, every NOT gate has exactly one input, and each gate has at most $k$ inputs, then the tree obtained by unfolding $C$ has size at most $(k+1)^{\mathrm{depth}(C)}$.

**Proof.** Apply the bound for unfolding a single vertex, which states that unfolding vertex $v$ with sufficient fuel has size at most $(k+1)^{\mathrm{depth}(v)}$ (`BoolCircuit.DAGCircuit.unfoldVertex_size_le`). The circuit tree is the unfolding of the output vertex with fuel large enough to cover its index. The output is a valid vertex, and its assigned depth is the circuit depth. Substituting the output vertex and this fuel into the single-vertex bound gives the result.

**Key facts.** `BoolCircuit.DAGCircuit.unfoldVertex_size_le`.
