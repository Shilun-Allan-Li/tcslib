<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: Language.InLayeredPPoly.inPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layered Polynomial Size Implies Polynomial Size

**Claim.** A language recognized by a finite layered-circuit family using standard gate operations and having polynomial size is recognized by a well-formed circuit family with fan-in at most two and polynomial size.

**Proof.** Take a finite layered family $C$ witnessing layered polynomial size, with size at most $a(n+1)^k$. Convert each layered circuit into a well-formed directed acyclic circuit $D$; this conversion preserves evaluation (`BoolCircuit.LayeredCircuit.toDAG_eval`), gives well-formedness (`BoolCircuit.LayeredCircuit.toDAG_isWellFormed`), and has size $n+\operatorname{size}(C_n)$ (`BoolCircuit.LayeredCircuit.toDAG_size`). Since $n+1$ and $(n+1)^k$ are each at most $(n+1)^{k+1}$, the size of $D$ is at most $(a+1)(n+1)^{k+1}$. Replace each gate of $D$ by a fan-in-two circuit using the binarization construction. It preserves evaluation (`BoolCircuit.DAGCircuit.binarize_eval`) and yields a well-formed fan-in-two circuit (`BoolCircuit.DAGCircuit.binarize_isFaninTwo`). Its size is bounded by $n+|D|(|D|+2)$ (`BoolCircuit.DAGCircuit.binarize_size_le`); using the preceding polynomial bound, this is at most $3(a+1)^2(n+1)^{2(k+1)}$. Finally, evaluation preservation at both conversion steps shows that the resulting family recognizes the same language. Hence it witnesses polynomial size in the fan-in-two circuit model.

**Key facts.** `Language.inLayeredPPoly_iff`, `Language.inPPoly_iff`, `BoolCircuit.LayeredCircuit.toDAG_isWellFormed`, `BoolCircuit.LayeredCircuit.toDAG_size`, `BoolCircuit.LayeredCircuit.toDAG_eval`, `BoolCircuit.DAGCircuit.binarize_size_le`, `BoolCircuit.DAGCircuit.binarize_isFaninTwo`, `BoolCircuit.DAGCircuit.binarize_eval`.
