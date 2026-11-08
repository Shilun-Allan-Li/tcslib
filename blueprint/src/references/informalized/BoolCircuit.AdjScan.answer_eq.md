<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjScan.answer_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency Scan Answers

**Claim.** Under the stated target and task-word hypotheses, the scan’s answer agrees with the indicator of membership in the language associated with the task.

**Proof.** Replace the language indicator by the decision of membership (`indicator_eq_decide`), and split according to the task. For a size query, the task word identifies the payload as $\operatorname{bits}(tv)$; membership is exactly $tv<\mathrm{size}(C_n)$ (`mem_sizeLang`). Since the size is $n+|\mathrm{gates}(C_n)|$, the scan returns true for $tv<n$, uses its default answer at input vertices, and returns true for gate indices precisely when they remain below the circuit size. These cases are equivalent. For a type query, membership means that $tv$ is a circuit vertex and its type equals the requested type (`mem_typeLang`). Below $n$, the vertex type is `none`; at or above $n$, it is the kind of the corresponding gate when that gate exists. Splitting at these boundaries shows that the default answer for input vertices and the gate-kind test for gate vertices produce exactly this membership decision; indices beyond the circuit have neither membership nor a positive scan answer. For an edge query, membership is exactly that the circuit has the edge from $iv$ to $tv$ (`mem_edgeLang`). Targets below $n$ cannot be gate targets, so the answer is false. For targets at or above $n$, the gate exists exactly when $tv-n$ is within the gate list, and then the scan tests whether $iv$ is in that gate’s argument list. Beyond the list the answer is again false. Thus each task’s scan answer equals its language indicator.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `BoolCircuit.DAGCircuitFamily.mem_sizeLang`, `BoolCircuit.DAGCircuitFamily.mem_typeLang`, `BoolCircuit.DAGCircuitFamily.mem_edgeLang`.
