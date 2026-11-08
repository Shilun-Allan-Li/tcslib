<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.exists_straightLine_and_not_dagCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-line conjunction and DAG size lower bound

**Claim.** A valid straight-line program of length one computes conjunction on two Boolean inputs, whereas no DAG circuit of size at most two computes that conjunction.

**Proof.** For the straight-line program, take one conjunction statement whose operands are the two input bits. It is valid because input operands are available before every line, and its evaluation is their conjunction. For the DAG claim, suppose a circuit on two inputs has size at most two. Since size is the number of input vertices plus the number of gates, it has no gates. Its output must therefore be one of the two input vertices. The value-at-an-input lemma (`DAGCircuit.values_getD_input`) shows that the circuit computes that selected input bit. If the output is the first input, evaluate at $(0,1)$; if it is the second, evaluate at $(1,0)$. In either case the circuit outputs $0$, while conjunction outputs $0$—wait, the contradiction requires the other assignment: for the first input choose $(1,0)$, and for the second choose $(0,1)$. Then the circuit outputs $1$ and conjunction outputs $0$, contradicting agreement.

**Key facts.** `BoolCircuit.DAGCircuit.values_getD_input`.
