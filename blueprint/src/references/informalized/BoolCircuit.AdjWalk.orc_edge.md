<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.orc_edge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Answer for Circuit Edges

**Claim.** On the encoding of $1^n$ together with the binary encodings of $u$ and $v$, the edge oracle returns the indicator of whether $u$ is an argument of the gate at vertex $v$ in the circuit for input length $n$.

**Proof.** The edge oracle is the Boolean indicator of the edge language. By the indicator-to-decision fact (`indicator_eq_decide`), its value on the given encoding is the decision of whether that encoding belongs to the edge language. The membership characterization of the edge language (`mem_edgeLang`) identifies this membership exactly with the edge relation from $u$ to $v$. Thus the oracle value is `decide` of that relation.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `BoolCircuit.DAGCircuitFamily.mem_edgeLang`.
