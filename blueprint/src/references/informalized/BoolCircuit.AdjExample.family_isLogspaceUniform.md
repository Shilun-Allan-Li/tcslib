<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample.lean :: BoolCircuit.AdjExample.family_isLogspaceUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Uniformity of the Example Family

**Claim.** The example circuit family is logspace-uniform: it has a polynomially bounded encoding function whose indexed bits and length predicate are decidable in logarithmic space, and that outputs the encoding of the circuit on unary input of length $n$.

**Proof.** First identify the family’s size language with the comparison language whose answer is true for every vertex index below $n+1$ (`family.sizeLang = leLang true true`). Next, for each gate type $t$, identify its type language with `leLang (decide (t = none)) (decide (t = some .or))`: input vertices have type `none`, and the sole gate, at index $n$, has type `.or`. Finally, the edge language is empty, since the example’s sole gate has no arguments. The proof of each identification unfolds the constant circuit and checks the indicated input or gate index. The family is canonical (`family_isCanonical`), so the characterization of logspace uniformity by logspace-decidable size, type, and edge languages applies (`isLogspaceUniform_iff`). Its size is bounded by $n+1$, and the three languages just identified are in logspace by the comparison-language result (`leLang_mem`). These facts give the required uniformity.

**Key facts.** `BoolCircuit.AdjExample.family_isCanonical`, `BoolCircuit.AdjExample.leLang_mem`, `BoolCircuit.DAGCircuitFamily.isLogspaceUniform_iff`.
