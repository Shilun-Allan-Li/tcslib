<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/Basic.lean :: FABL.boundaryEdgeFraction_eq_totalInfluence_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boundary Fraction and Influence

**Claim.** For a Boolean-valued function, the proportion of cube edges crossing between its two values equals its total influence divided by the dimension.

**Proof.** Expand the definitions of boundary edge fraction and total influence. Both are sums over coordinates, with the same factor of the dimension left outside the sum. For each coordinate, Fact 2.14 identifies the Boolean influence with the fraction of boundary edges in that coordinate. Fact 2.29 identifies that Boolean influence with the real-valued influence of the function. Applying these two identities term by term makes the sums equal, proving the claimed formula.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_eq_dimensionEdgeBoundaryFraction`.
