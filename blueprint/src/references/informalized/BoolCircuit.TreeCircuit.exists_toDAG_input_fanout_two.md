<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.TreeCircuit.exists_toDAG_input_fanout_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Input Use After Compilation

**Claim.** There is a circuit tree on one variable whose associated acyclic circuit has fanout exactly $2$ at input vertex $0$.

**Proof.** Take an AND node whose two children are the positive and negated literals of its sole variable, indexed by $0$. In the compiled circuit, each literal gate reads input vertex $0`; the fanout counts gates that read a vertex, so this input is read by exactly those two gates. Hence its fanout is $2$.
