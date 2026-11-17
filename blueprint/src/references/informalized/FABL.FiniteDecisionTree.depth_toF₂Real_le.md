<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.depth_toF₂Real_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under binary conversion

**Claim.** For a finite decision tree over sign-valued inputs and outputs, the associated binary decision tree has depth at most the original tree’s depth.

**Proof.** Proceed by induction on the tree. A leaf converts to a leaf, so both depths are zero. At a query, the converted tree has two children, corresponding to the signs $1$ and $-1$. By the induction hypothesis, each converted child has depth at most the depth of its original child; each original child’s depth is at most the maximum depth among all alphabet-labelled children. Thus the maximum of the two converted child depths is at most the original maximum child depth. Adding one for the root query gives the desired inequality.
