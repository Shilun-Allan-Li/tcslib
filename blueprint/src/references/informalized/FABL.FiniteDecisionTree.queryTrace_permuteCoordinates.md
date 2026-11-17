<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.queryTrace_permuteCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace Under Coordinate Permutation

**Claim.** For a tree with all coordinates available, permuting its coordinates by $\sigma$ makes its query trace on $x$ equal to the original tree’s trace on $i\mapsto x(\sigma(i))$, with $\sigma$ applied to every coordinate in that trace.

**Proof.** Unfold the definition of the permuted tree. Its root query, when present, is the image under $\sigma$ of the original root query. The child selected on input $x$ is therefore the child selected in the original tree by the value $x(\sigma(i))$ at the original query coordinate $i$. The recursive permutation of that child changes its available set by the corresponding image; casting between equal available sets does not change its trace (`queryTrace_castAvailable`). Applying the same reasoning down the selected branch gives the original trace on the reindexed input, with $\sigma$ applied to each entry. At a leaf both traces are empty.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_castAvailable`.
