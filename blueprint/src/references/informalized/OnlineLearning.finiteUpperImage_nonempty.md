<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.finiteUpperImage_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonemptiness of the finite upper image

**Claim.** If $X$ is nonempty, then the finite upper image is nonempty.

**Proof.** Choose any $x\in X$ and define the vector $z$ by $z_y=f(x,y)+1$ for each sampled column $y$. Then $f(x,y)<z_y$ at every coordinate, so this row witnesses that $z$ belongs to the finite upper image.
