<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.deterministicQueryProbability_eq_structural -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Structural query probability

**Claim.** Under the stated finite orthonormal-basis assumptions, the probability that a tree queries a given coordinate equals its structural query probability.

**Proof.** Induct on the tree, keeping the coordinate $i$ arbitrary. For a leaf, the query trace is empty and the structural probability is zero; the expectation of the constant zero is zero (pmfExpectation_const). At a query of coordinate $j$, first consider $i=j$: the trace contains $i$ immediately, and the structural probability is one, so both sides are the expectation of the constant one (pmfExpectation_const). If $i\ne j$, the root itself does not query $i$. The event that $i$ occurs in the trace is therefore exactly the event that it occurs in the selected child’s trace. For each fixed child value $\omega$, this event is unchanged when the input’s $j$th coordinate is replaced by $\omega$, because the child tree has no access to $j$ (FiniteDecisionTree.queries_replaceCoordinate_of_not_mem). The product-mean diagonal-section identity then averages first over the coordinate value and then over the remaining input, expressing the query probability as the expectation over $\omega$ of the child’s query probability (FiniteDecisionTree.productMean_diagonal_section). Applying the induction hypothesis to each child identifies that inner probability with the child’s structural query probability. This is precisely the recursive definition of the structural query probability at the root.

**Key facts.** `FABL.pmfExpectation_const`, `FABL.FiniteDecisionTree.queries_replaceCoordinate_of_not_mem`, `FABL.FiniteDecisionTree.productMean_diagonal_section`.
