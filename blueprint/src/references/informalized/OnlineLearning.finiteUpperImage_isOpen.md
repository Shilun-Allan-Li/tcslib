<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.finiteUpperImage_isOpen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Openness of the finite upper image

**Claim.** The finite upper image is open in the space of vectors indexed by the finite column sample.

**Proof.** For each fixed row $x\in X$, the vectors $z$ satisfying $f(x,y)<z_y$ for every sampled column are the intersection, over those columns, of the inverse images of the open intervals $(f(x,y),\infty)$ under the coordinate evaluation maps. Each coordinate map is continuous, so each inverse image is open; the intersection is finite and therefore open. The finite upper image is the union of these open sets over all rows $x\in X$, hence is open.
