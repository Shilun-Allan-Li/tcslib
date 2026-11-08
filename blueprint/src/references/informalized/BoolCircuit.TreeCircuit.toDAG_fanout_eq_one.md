<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.TreeCircuit.toDAG_fanout_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout of non-output gates

**Claim.** For a vertex $v$ with $n\le v<\mathrm{size}(c\text{ compiled})$ that is not the output, the number of gates reading $v$ is exactly $1$.

**Proof.** The fanout specification for the compiled DAG provides an exact-one condition for indices at least $n+|G|$ and less than $n+|G|+|G|$, excluding the output. Here the compilation starts with no gates, so this condition applies to the compiled gate list; the size of the DAG is $n+|G|$. The assumed bounds on $v$ therefore put it in the interval required by the specification, and the non-output hypothesis excludes its exceptional index. Hence its fanout is $1$.

**Key facts.** `BoolCircuit.TreeCircuit.toDAG_fanoutSpec`.
