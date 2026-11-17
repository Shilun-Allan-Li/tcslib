<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.compileTrees_fanout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout of Compiled Circuit Lists

**Claim.** If every tree in a list has the stated single-circuit fanout behavior when compiled after an acyclic gate list, then compiling the entire list appends gates satisfying the corresponding list-level fanout properties.

**Proof.** Induct on the list. For the empty list, compilation appends no gates and produces no roots, so the fanout conditions hold with all counts zero. For a nonempty list $c::cs$, first compile $c$, obtaining an extension $e_1$ and its root; then compile $cs$ after that intermediate gate list, obtaining an extension $e_2$ and the remaining roots. The single-tree assumption gives the first compilation's fanout properties, and the induction hypothesis gives the list properties for the second compilation. The single-tree specification ensures the intermediate list is acyclic (`BoolCircuit.compileTree_spec`), as required to apply the induction hypothesis. The extensions concatenate, and fanout counts add over concatenation (`BoolCircuit.fanoutIn_append`).

For vertices belonging to the original gate range, both extensions contribute zero by their old-vertex unread conditions. For any vertex of index at least $n$, split according to whether it lies before the end of the first intermediate list. In that range the second extension contributes zero as an old vertex, and the first contributes at most one. Beyond that range, acyclicity ensures the first extension contributes zero (`BoolCircuit.fanoutIn_ext_eq_zero`), and the second contributes at most one. Each listed root is unread in the combined extension: the first root is unread by the first compilation and is an old vertex for the second; any later root is unread by the induction hypothesis, while the first extension contributes zero at its index because it is beyond the first intermediate list. The root-location condition follows by combining the first compilation's location with the induction hypothesis's location for subsequent roots. Finally, a new vertex not among the listed roots is either in the first extension's new range, where it is read exactly once by the first compilation and not by the second, or in the second extension's new range, where it is read exactly once by the induction hypothesis and not by the first. The latter exclusion follows because that vertex lies beyond the first intermediate list.

**Key facts.** `BoolCircuit.compileTree_spec`, `BoolCircuit.fanoutIn_append`, `BoolCircuit.fanoutIn_ext_eq_zero`.
