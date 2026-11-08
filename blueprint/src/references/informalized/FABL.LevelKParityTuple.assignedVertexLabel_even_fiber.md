<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.LevelKParityTuple.assignedVertexLabel_even_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Even Label-Fiber Size

**Claim.** For every label $x$, the number of vertices assigned label $x$ is even.

**Proof.** Fix a label $x$. The proof first identifies the fiber of vertices labeled $x$ with the disjoint union, over parts, of the positions in that part whose enumerated element is $x$. The bijection preserves cardinality, so it suffices to count those positions. In each part the enumeration is a bijection from the $k$ positions onto that part's set; reordering the positions is also a bijection. Thus the number of positions labeled $x$ in that part is one exactly when $x$ belongs to the part's set, and zero otherwise. Summing over the parts reduces the fiber cardinality to the number of sets in the tuple containing $x`. The finite-subtype counting formula (`natCard_subtype_eq_countP_ofFn`) expresses this number as the count of such parts, and the parity consequence of empty tuple symmetric difference (`even_countP_of_tupleSymmDiff_eq_empty`) says that this count is even. Therefore the label fiber has even cardinality.

**Key facts.** `FABL.natCard_subtype_eq_countP_ofFn`, `FABL.even_countP_of_tupleSymmDiff_eq_empty`.

**Caveat.** The source proof uses `tuple.assignedLabelFiberEquivPartFiber` to identify the vertex fiber with the relevant part-position fibers, but that lemma is not included in the supplied upstream facts. The reduction is described from the stated construction, but its exact content is not available here.
