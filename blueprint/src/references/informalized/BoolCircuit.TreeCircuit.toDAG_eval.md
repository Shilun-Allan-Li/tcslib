<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.TreeCircuit.toDAG_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by translation

**Claim.** For every Boolean circuit $c$ on $n$ variables and every Boolean assignment $x$, evaluating the DAG translation of $c$ at $x$ gives the same value as evaluating $c$ at $x$.

**Proof.** Begin the compilation with the empty gate list, which is acyclic. The compilation specification (BoolCircuit.compileTree_spec) then applies and supplies its value-preservation property: for every assignment $x$, the compiled DAG evaluates to the same Boolean value as the original tree circuit. This is the claimed equality.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.compileTree_spec`.
