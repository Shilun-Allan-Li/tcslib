<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.rewriteGates_binarize_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Gate Binarization

**Claim.** For an acyclic gate list in which every gate has at most $K$ arguments and each NOT gate has exactly one argument, binarizing the list produces a gate list whose length is at most the sum over the original gates of $\max(1,\text{number of arguments}-1)$.

**Proof.** Use induction on the gate list, adding its final gate $g$ after the preceding list. The preceding list remains acyclic and satisfies the same gate-shape bounds, so the induction bound applies to its rewritten list. The invariant for rewriting gives a map of earlier vertices to rewritten vertices that preserves their range and ensures that every transformed argument of $g$ is a valid earlier vertex (`rewriteGates_inv`). Deduplication can only shorten the argument list.

If $g$ is a NOT gate, its one-argument hypothesis makes binarization append exactly one gate. This contributes at most $\max(1,|g.args|-1)=1$. If $g$ is an AND or OR gate, the emitted tree gadget has length bounded by its tree cost (`emitTree_spec`). The number of distinct transformed arguments is at most the original argument count, and the tree-cost estimate bounds this contribution by $\max(1,|g.args|-1)$ (`treeCost_le_max`). Thus in every case the final rewrite adds no more than the summand assigned to $g$. Adding this to the induction bound proves the claimed sum bound.

**Key facts.** `BoolCircuit.binarizeGadget_correct`, `BoolCircuit.rewriteGates_inv`, `BoolCircuit.emitTree_spec`, `BoolCircuit.treeCost_le_max`.
