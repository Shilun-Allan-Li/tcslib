<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.deterministicAverageCost_permuteCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average cost under coordinate permutations

**Claim.** Permuting the coordinates of a finite decision tree does not change its average query cost under independent inputs with a common distribution on the finite alphabet.

**Proof.** Write the average cost as the product mean of the tree’s query count. At each input $x$, the permuted tree’s query count equals the original tree’s query count on the input whose $j$th coordinate is $x_{σ(j)}$ (FiniteDecisionTree.queryCount_permuteCoordinates). Hence the integrand for the permuted tree is the original integrand composed with this coordinate reindexing. The product distribution with identical coordinate marginals is invariant under coordinate permutations, so these two product means agree (productMean_comp_permuteInput).

**Key facts.** `FABL.FiniteDecisionTree.queryCount_permuteCoordinates`, `FABL.productMean_comp_permuteInput`.
