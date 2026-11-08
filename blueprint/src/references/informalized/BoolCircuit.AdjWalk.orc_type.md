<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformWalk.lean :: BoolCircuit.AdjWalk.orc_type -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Type Query for Encoded Vertices

**Claim.** Whenever query index $j$ selects the type language for $t$, the oracle on the encoding of $1^n$ paired with the binary expansion of $v$ returns true exactly when $v$ is within the circuit's size and has type $t$.

**Proof.** By the definition of the oracle as the indicator of the selected query language, and the hypothesis that query $j$ selects the type language for $t$, the oracle value is the decision of membership in that type language (`indicator_eq_decide`). The membership characterization for the type language (`mem_typeLang`) says that the given encoding belongs precisely when both $v<\mathrm{size}(C_n)$ and the type of vertex $v$ is $t$. Hence the oracle value is the decision of their conjunction.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `BoolCircuit.DAGCircuitFamily.mem_typeLang`.
