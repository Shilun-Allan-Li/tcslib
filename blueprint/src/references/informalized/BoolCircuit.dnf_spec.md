<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.dnf_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of the DNF Construction

**Claim.** For every natural number $n$ and Boolean function $f$, the DNF construction first emits conjunction trees for the minterm leaves of the satisfying assignments, then emits an OR tree on their resulting vertices. The final gate list extends the initial negation gates and is acyclic, its output is a valid vertex, and its output value, size bound, depth bound, and properties of newly added gates satisfy the stated specification.

**Proof.** Apply the general specification for emitting a tree (BoolCircuit.emitTree_spec) to the final OR tree. Its gate kind is not negation, as required by that theorem. The initial gate list for this final stage is the list produced by the minterm construction. The minterm-tree specification (BoolCircuit.minterms_spec) supplies the acyclicity of that list and the fact that all vertices fed into the OR tree are valid relative to it. With these hypotheses, the tree-emission theorem gives the extension property, acyclicity, a valid output vertex, the output-value identity, the bound on added gates, the depth bound, and the stated form and fan-in of newly added gates. This resulting tree is exactly the final stage of the DNF construction, so these conclusions give the claimed specification.

**Key facts.** `BoolCircuit.minterms_spec`, `BoolCircuit.emitTree_spec`.
