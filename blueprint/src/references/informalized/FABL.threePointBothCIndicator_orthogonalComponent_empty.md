<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.threePointBothCIndicator_orthogonalComponent_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Component of the Two-Coordinate Indicator

**Claim.** The Fourier component supported on the empty coordinate set is the constant function with value $1/9$.

**Proof.** Use the Möbius formula for an orthogonal component ( `FiniteFourierBasis.orthogonalComponent_eq_mobius`). When the support set is empty, its only subset is the empty set, so the component is just the projection onto no coordinates. The projection formula for the two-coordinate indicator ( `projectOnCoordinates_threePointBothCIndicator`) gives a factor of $1/3$ at each coordinate when neither coordinate is retained. Their product is $1/9$, independent of the input point, proving the claim.

**Key facts.** `FABL.FiniteFourierBasis.orthogonalComponent_eq_mobius`, `FABL.projectOnCoordinates_threePointBothCIndicator`.
