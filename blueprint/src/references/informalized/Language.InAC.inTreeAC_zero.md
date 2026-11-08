<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InAC.inTreeAC_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-Zero AC Tree Conversion

**Claim.** Every language recognized by a well-formed polynomial-size circuit family of depth at most a constant is recognized by a polynomial-size tree-circuit family whose depth is also bounded by a constant.

**Proof.** Choose a well-formed circuit family $C$ witnessing the hypothesis, with size bound $a(n+1)^k$ and depth bound $b$. Replace each circuit by its tree expansion. The expansion preserves the recognized language (the circuit-family language preservation theorem, `BoolCircuit.DAGCircuitFamily.language_toTree`). Its depth is at most the original circuit depth (`BoolCircuit.DAGCircuit.toTree_depth_le`), hence at most $b$. For size, well-formedness gives an upper bound on every gate's number of arguments by the circuit size (`BoolCircuit.DAGCircuit.args_length_le_size`). The tree expansion bound therefore gives size at most $(s+1)^d$, where $s$ and $d$ are the original size and depth. Since $d\le b$, this is at most $(s+1)^b$. From $s\le a(n+1)^k$ and $(n+1)^k\ge1$, we have $s+1\le(a+1)(n+1)^k$, so the tree size is at most $(a+1)^b(n+1)^{kb}$. Thus the expanded family has polynomial size and constant depth, as required.

**Key facts.** `BoolCircuit.DAGCircuit.args_length_le_size`, `BoolCircuit.DAGCircuit.toTree_size_le`, `BoolCircuit.DAGCircuit.toTree_depth_le`, `BoolCircuit.DAGCircuitFamily.language_toTree`.
