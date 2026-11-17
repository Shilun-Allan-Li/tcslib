<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGCircuit.eval_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Canonical Circuit

**Claim.** For any directed acyclic Boolean circuit $C$ with $n$ inputs, its canonical form has the same evaluation as $C$ on every input assignment.

**Proof.** Fix an input assignment $x$. The circuit evaluation reads the value list produced by running its gates, then selects the output vertex. Canonicalization replaces each gate by its canonical version while preserving its evaluation on every value list (`BoolCircuit.DAGGate.eval_canon`). Consequently, the gate-by-gate run on the canonical gates produces exactly the same value list as the original run: this is the fold-preservation property `BoolCircuit.runWith_map`. Since both circuits select the same output vertex from those identical lists, their evaluations agree at $x$. As $x$ was arbitrary, the evaluations are equal as functions.

**Key facts.** `BoolCircuit.DAGGate.eval_canon`, `BoolCircuit.runWith_map`.
