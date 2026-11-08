<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandRandomizedTree_inputCost_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive NAND Input-Cost Recurrence

**Claim.** For each input at level $d+1$, the randomized tree's expected query cost is the stated average of the two possible block orders: it pays for the first block and, unless that block's output is $+1$, also pays for the second block.

**Proof.** The seed at level $d+1$ chooses uniformly between the two block orders and independently supplies recursive seeds for the two level-$d$ trees. First average the query count over the recursive seeds using the expectation rules for sequential sampling and for mapping a random seed to its tree; these rules express the cost as the average, over the two orders, of the corresponding expected deterministic query counts. For either order, the tree queries the first block and continues to the other block exactly when the first block's recursive NAND value is not $+1$. The query-count decomposition for the recursive tree (\(\texttt{FABL.queryCount_recursiveNandTree_succ}\)) supplies these two cases. Averaging over the two equally likely orders gives the displayed formula. The expectation identities used here are: expectation commutes with sampling in stages (\(\texttt{FABL.pmfExpectation_bind}\)), expectation under a mapped seed is expectation after composition (\(\texttt{FABL.pmfExpectation_map}\)), and the uniform two-point seed averages the two order costs (\(\texttt{FABL.pmfExpectation_uniformPMF_eq_expect}\)). The remaining constant-term expectation identities (\(\texttt{FABL.pmfExpectation_const}\), \(\texttt{FABL.pmfExpectation_add_const_general}\), and \(\texttt{FABL.pmfExpectation_const_add_general}\)) account for the zero continuation cost and regroup the terms.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.pmfExpectation_map`, `FABL.queryCount_recursiveNandTree_succ`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_add_const_general`, `FABL.pmfExpectation_const_add_general`.
