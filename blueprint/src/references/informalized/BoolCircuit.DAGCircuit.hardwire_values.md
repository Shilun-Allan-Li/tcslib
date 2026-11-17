<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.hardwire_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values After Hardwiring

**Claim.** Evaluating the circuit obtained by hardwiring $y$ at $x$ produces the same list of vertex values as evaluating the original circuit at the concatenated assignment $(x,y)$.

**Proof.** The hardwired gate list consists of the $m$ constant gates for the values in $y$, followed by the original gates. Running a circuit over a concatenation of gate lists is the same as first running the first list and then running the second (`BoolCircuit.runWith_append`). The constant gates append precisely their assigned Boolean values to the initial list of vertex values (`BoolCircuit.runWith_eval_constGates`), so after processing them the values are those from $x$ followed by those from $y$. This is exactly the list of input values associated with the concatenated assignment $(x,y)$; running the original gates from that list therefore gives the claimed equality.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_eval_constGates`.
