<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.rewriteInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation in One Rewrite Step

**Claim.** If a state satisfies the rewrite invariant for an acyclic original list, then appending an eligible gate $g$ whose addition preserves acyclicity and rewriting it once yields a state satisfying the invariant for the enlarged list.

**Proof.** Let the old list have $m$ gates. Acyclicity of the enlarged list implies that every argument of $g$ refers to an index below $n+m$. Use the old vertex map to replace each such argument by its rewritten vertex, forming a remapped gate $g'$. The old invariant ensures these mapped arguments are available in the rewritten list, which is acyclic; thus gadget correctness applies to $g'$ and the current rewritten list. Its gadget specification supplies an extended acyclic list, a valid output vertex, the output value and depth bounds, a size bound, and property $P$ for newly emitted gates.

The new map appends the gadget's output vertex. For every earlier vertex, its map entry is unchanged, and execution on either the old or rewritten list leaves earlier vertices' values and depths unchanged; these are the append-preservation facts (`runWith_append`, `runWith_getD_of_lt`, `vertexValue_append`, and `vertexDepth_append`). At the newly added vertex, the gadget specification gives the value of $g'$, and remapping preserves gate evaluation because each mapped input has the same value as its original input (`DAGGate.eval_remap`). The gadget output is therefore the value of $g$ in the original execution (`runWith_getD_last`).

For depth at the new vertex, the gadget depth bound contributes $c$ plus the maximum depth of the remapped arguments. Each such depth is bounded by $c$ times the corresponding old depth, and each old argument depth is at most the maximum over all arguments (`le_foldr_max'`, followed by `foldr_max_le'`). Combining these inequalities with the old output-depth formula yields the required factor-$c$ bound. Finally, the gadget's length bound adds at most $g.args.length+2$ gates, and its property for newly emitted gates together with the old invariant gives $P$ for every gate in the resulting list.

**Key facts.** `BoolCircuit.runWith_append`, `BoolCircuit.runWith_getD_of_lt`, `BoolCircuit.vertexValue_append`, `BoolCircuit.vertexDepth_append`, `BoolCircuit.DAGGate.eval_remap`, `BoolCircuit.runWith_getD_last`, `BoolCircuit.le_foldr_max'`, `BoolCircuit.foldr_max_le'`.
