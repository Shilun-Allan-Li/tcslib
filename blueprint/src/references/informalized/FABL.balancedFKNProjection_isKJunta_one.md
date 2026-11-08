<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.balancedFKNProjection_isKJunta_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-coordinate dependence

**Claim.** The projection obtained by evaluating the signed coordinate function at vectors whose first coordinate is $1$ depends on at most one coordinate.

**Proof.** Split according to whether the chosen coordinate is the first coordinate. In the first case, every vector of the form $(1,x)$ has that coordinate equal to $1$, so the signed dictator takes a constant value, whether or not it is negated. It therefore depends on the empty set of coordinates, which has size at most one. In the other case, write the chosen coordinate as the first coordinate of the remaining vector, say $j$. If two inputs agree on $j$, then their extensions by the initial $1$ agree at the chosen coordinate; consequently the signed dictator has the same value on both. Thus it depends only on the singleton set containing $j$.
