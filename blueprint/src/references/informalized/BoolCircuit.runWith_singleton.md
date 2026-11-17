<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Single Gate

**Claim.** Evaluating the one-gate list $[g]$ from $init$ appends $f(g,init)$ to $init$.

**Proof.** The fold processes its sole gate by appending its output to the current list. Starting from $init$, this gives $init++[f(g,init)]$.
