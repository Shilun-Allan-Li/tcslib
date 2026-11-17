<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean :: measurableSet_badSingle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the distortion event

**Claim.** For a measurable matrix-valued map $A$, fixed vector $x$, and real $\varepsilon$, the set of outcomes where $x$ is badly distorted is measurable.

**Proof.** Each matrix entry of $A(\omega)$ is measurable, since coordinate projections preserve measurability. For each output coordinate, applying $A(\omega)$ to the fixed vector $x$ gives a finite sum of measurable matrix entries multiplied by constants, hence a measurable function. The squared norm of the resulting vector is a finite sum of squares of these coordinates, so it too is measurable. Subtracting the constant $\|x\|^2$ and taking absolute value preserves measurability. The distortion event is the strict sublevel comparison between the constant $\varepsilon\|x\|^2$ and this measurable absolute difference, and is therefore measurable.
