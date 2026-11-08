<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.f₂DotProduct_f₂UnitVector -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dot Product with a Coordinate Unit Vector

**Claim.** For a vector $x$ and coordinate $i$, its dot product with the unit vector supported at $i$ equals $x_i$.

**Proof.** In the dot-product sum, the unit vector has value $1$ at coordinate $i$ and $0$ at every other coordinate. Thus every summand vanishes except the one indexed by $i$, which equals $x_i$.
