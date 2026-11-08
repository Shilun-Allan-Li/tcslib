<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.andAllDAG_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the AND Circuit

**Claim.** For every natural number $n$ and Boolean assignment $x$ on the $n$ input vertices, the circuit formed by combining all inputs with AND evaluates to true exactly when every input is true.

**Proof.** The specification of the emitted AND tree identifies its output value with the evaluation of an AND gate whose arguments are the list of input vertices (`BoolCircuit.andAllDAG_spec`). The circuit evaluation reads that output from the run of its gates; the empty gate list in the initial construction leaves the initial input values unchanged (`BoolCircuit.runWith_nil`). Consequently, the output is the conjunction over the entries of `List.range n`, with each entry $a$ contributing the value $x(a)$. This conjunction is true exactly when every $a<n$ has $x(a)=\mathrm{true}$. Such indices are exactly the elements of the type of input indices, so this is equivalent to every input being true.

**Key facts.** `BoolCircuit.andAllDAG_spec`, `BoolCircuit.runWith_nil`.
