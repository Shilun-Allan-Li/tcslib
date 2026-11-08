<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyGadget.lean :: BoolCircuit.gadget_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Boolean Gadget

**Claim.** For every natural number $m$, Boolean function $f$ on assignments to $m$ variables, and assignment $x$, the gadget constructed from $f$ outputs $f(x)$.

**Proof.** The gadget is obtained by first converting the universal tree circuit for $f$ to a DAG and then binarizing that DAG. Binarization preserves evaluation, so the gadget’s value on $x$ equals the value of the DAG obtained from the universal tree. The tree-to-DAG translation also preserves evaluation, reducing the claim to the universal tree circuit. That circuit evaluates to $f(x)$, giving the desired equality.

**Key facts.** `BoolCircuit.DAGCircuit.binarize_eval`, `BoolCircuit.TreeCircuit.toDAG_eval`, `BoolCircuit.universalCircuit_eval`.
