<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.depth_truncate_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bound after truncation

**Claim.** Truncating a decision tree with fallback value $a$ at parameter $k$ produces a tree of depth at most $k$.

**Proof.** Proceed by induction on the tree. A leaf remains a leaf, so its truncated depth is zero and is at most $k$. For a query, first consider $k=0$: truncation replaces the query by a leaf, whose depth is zero. If $k$ is positive, write it as $j+1$. The truncated tree retains the query and truncates each child at parameter $j$. By induction, both truncated child depths are at most $j$. Their maximum is therefore at most $j$, so the depth of the retained query is at most $j+1=k$.
