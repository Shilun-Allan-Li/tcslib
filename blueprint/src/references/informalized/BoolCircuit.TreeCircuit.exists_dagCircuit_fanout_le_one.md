<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.TreeCircuit.exists_dagCircuit_fanout_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Fanin Tree Compilation

**Claim.** A tree whose maximum fanin is at most $2$ has an equivalent acyclic circuit with fanin at most $2$, no repeated input to a gate, exactly one input to each NOT gate, fanout at most one for every non-input vertex, and size at most $n+\mathrm{size}(c)$.

**Proof.** Take the acyclic circuit obtained by compiling the tree, denoted $c.toDAG$. The compilation satisfies the well-formedness and fanin-at-most-two conditions whenever the tree's maximum fanin is at most two (`BoolCircuit.TreeCircuit.toDAG_isFaninTwo`). Every vertex with index at least $n$ is read by at most one gate (`BoolCircuit.TreeCircuit.toDAG_fanout_le_one`). The compiled circuit has the same evaluation as the tree on every assignment (`BoolCircuit.TreeCircuit.toDAG_eval`), and its size is at most $n+\mathrm{size}(c)$ (`BoolCircuit.TreeCircuit.toDAG_size_le`). These properties give the required circuit.

**Key facts.** `BoolCircuit.TreeCircuit.toDAG_isFaninTwo`, `BoolCircuit.TreeCircuit.toDAG_fanout_le_one`, `BoolCircuit.TreeCircuit.toDAG_eval`, `BoolCircuit.TreeCircuit.toDAG_size_le`.
