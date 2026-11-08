<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeDAG.lean :: BoolCircuit.compileTrees_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of List Compilation

**Claim.** Under the assumed single-tree compilation specifications, compiling a list of trees extends the initial acyclic gate list and produces one valid root per tree, with the stated value, size, depth, and gate-shape bounds.

**Proof.** Induct on the list of trees. For the empty list, compilation changes nothing and produces no roots, so all assertions follow from the empty-list identities, including the zero sum of sizes (`BoolCircuit.TreeCircuit.sumSize_nil`). For a nonempty list $c::cs$, compile $c$ after the initial list, obtaining $r_1$, then compile $cs$ after the gates in $r_1$, obtaining $r_2$. The assumed single-tree specification applies to the first compilation; the induction hypothesis applies to the second because the first resulting gate list is acyclic. Their extensions concatenate, and the second result is acyclic, giving an acyclic extension of the original list.

The root list consists of the first root followed by the roots from $r_2$. The first root remains in range after the second compilation because the gate list only grows; the other roots are in range by induction. For values, the second compilation's roots agree with the evaluations of $cs$. The first root's value is unchanged by appending the later gates, by preservation of earlier vertex values (`BoolCircuit.vertexValue_append`), and its original value is the evaluation of $c$. Together these establish the ordered list of values. The length bound follows by combining the two compilation bounds and the sum decomposition (`BoolCircuit.TreeCircuit.sumSize_cons`). Each root has the depth bound: the first root's depth is preserved under extension (`BoolCircuit.vertexDepth_append`), while the other roots satisfy the induction bound; both are bounded by the maximum depth of the full list plus one (`BoolCircuit.TreeCircuit.maxDepth_cons`). Finally, every new gate belongs to one of the two extensions, so its well-formedness is inherited from the corresponding compilation. Each fan-in bound is at most the maximum for the full list, by the decomposition of maximum fan-in (`BoolCircuit.TreeCircuit.maxFaninL_cons`).

**Key facts.** `BoolCircuit.TreeCircuit.sumSize_nil`, `BoolCircuit.vertexValue_append`, `BoolCircuit.vertexDepth_append`, `BoolCircuit.TreeCircuit.sumSize_cons`, `BoolCircuit.TreeCircuit.maxDepth_cons`, `BoolCircuit.TreeCircuit.maxFaninL_cons`.
