<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBiasMarginals.lean :: FABL.coordinateProjectionLinear_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate projection formula

**Claim.** For a subset $J$ of the coordinates and a vector $x$ over $\mathbb F_2$, the linear coordinate projection onto $J$, evaluated at position $q$, equals $x$ at the coordinate corresponding to $q$ in the increasing enumeration of $J$.

**Proof.** The coordinate projection is defined pointwise: at position $q$ it returns the value of the input vector at the coordinate selected by the inverse of the increasing enumeration $J\simeq\{0,\ldots,|J|-1\}$. The claimed formula is therefore the definition of the projection.
