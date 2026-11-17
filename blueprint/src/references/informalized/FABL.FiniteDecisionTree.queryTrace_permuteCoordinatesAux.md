<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.queryTrace_permuteCoordinatesAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Auxiliary Permutation Trace Formula

**Claim.** For any available set, tree, coordinate permutation $\sigma$, and input $x$, the permuted tree’s trace equals the original tree’s trace on $i\mapsto x(\sigma(i))$, with $\sigma$ applied to each entry.

**Proof.** Proceed by induction on the tree. For a leaf, both traces are empty. At a query node with coordinate $i$, the permuted tree first queries $\sigma(i)$, then follows the child selected by $x(\sigma(i))$. The recursive permutation construction casts the child to its image available set, and this cast leaves its trace unchanged (`queryTrace_castAvailable`). The induction hypothesis applied to that selected child and the same input identifies the remaining trace with the original child’s trace on $j\mapsto x(\sigma(j))$, mapped entrywise by $\sigma$. Prefixing the root coordinate on each side proves the formula.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_castAvailable`.
