<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.recursiveMajorityThreeBlocksEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Recursive Block Equivalence

**Claim.** For every depth $d$, sign vector $x$ of length $3^{d+1}$, and $i\in\mathrm{Fin}(3)$, evaluating the block decomposition of $x$ at $i$ gives the vector of coordinates of $x$ in the $i$th block of length $3^d$.

**Proof.** The block equivalence is defined by reindexing the coordinates of $x$ according to the product decomposition of the larger index set, then currying the resulting function into its first and second coordinates. Evaluating the curried function at $i$ and then at a coordinate $j$ returns the value of $x$ at the coordinate corresponding to the pair $(i,j)$. This is exactly the definition of the input block associated with $i$, so the two vectors agree at every coordinate and hence are equal.
