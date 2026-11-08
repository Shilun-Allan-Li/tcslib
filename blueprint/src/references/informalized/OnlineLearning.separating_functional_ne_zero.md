<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.separating_functional_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Separating Functional Is Nonzero

**Claim.** If the upper image is nonempty and every point in it has strictly smaller functional value than the fixed vector, then the separating functional is nonzero.

**Proof.** Suppose instead that $L$ is the zero functional. By nonemptiness of the finite upper image (`finiteUpperImage_nonempty`), choose a point $z$ in it. The strict separation hypothesis gives $L(z)<L(c)$, but the zero functional takes the value $0$ on both vectors, a contradiction. Hence $L\ne 0$.

**Key facts.** `OnlineLearning.finiteUpperImage_nonempty`.
