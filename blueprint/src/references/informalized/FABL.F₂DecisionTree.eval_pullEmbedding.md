<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.eval_pullEmbedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under Coordinate Pullback

**Claim.** Pulling a tree back along an injection and evaluating at $x$ agrees with evaluating the original tree on the input that places $x_i$ at coordinate $e(i)$ and zero elsewhere.

**Proof.** Proceed by induction on the original tree, generalizing the source coordinate set. Leaves give the same stored output. At a query of coordinate $j$, first consider the case that $j=e(i)$ for some source coordinate $i$. The pulled-back tree queries that $i$, and the extended input has value $x_i$ at $j$ by injectivity of $e$. Thus both trees choose the same branch; the induction hypothesis for that child proves equality. If $j$ is not in the image of $e$, the pulled-back construction discards this query and continues with the zero-child. The extended input has value zero at $j$, so the original tree also follows its zero-child. The induction hypothesis again gives the equality.
