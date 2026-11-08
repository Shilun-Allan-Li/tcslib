<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.TreeCircuit.toLayered_eval₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Layered Circuit

**Claim.** For an input assignment $x$, evaluating the layered circuit associated to $c$ on the input obtained by mapping Boolean values into $\mathrm{Fin}\,2$ gives the value of $c$ on $x$, mapped into $\mathrm{Fin}\,2$.

**Proof.** Rewrite the tree's layered circuit as the layered embedding of its compiled directed acyclic circuit. The evaluation theorem for layered circuits applies because every gate in the De Morgan transformed circuit is not an OR gate (`BoolCircuit.DAGCircuit.deMorgan_kind_ne_or`); it identifies the layered evaluation with evaluation of that transformed circuit. By preservation of evaluation under De Morgan transformation (`BoolCircuit.DAGCircuit.deMorgan_eval`), this is the evaluation of the compiled circuit, which equals the tree's direct evaluation (`BoolCircuit.TreeCircuit.toDAG_eval`). Mapping the resulting Boolean value into $\mathrm{Fin}\,2$ yields the stated equality.

**Key facts.** `BoolCircuit.DAGCircuit.deMorgan_kind_ne_or`, `BoolCircuit.DAGCircuit.toLayered_eval₁`, `BoolCircuit.DAGCircuit.deMorgan_eval`, `BoolCircuit.TreeCircuit.toDAG_eval`.
