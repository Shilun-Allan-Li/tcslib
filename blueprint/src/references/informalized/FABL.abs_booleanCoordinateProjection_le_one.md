<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.abs_booleanCoordinateProjection_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Projection Bound

**Claim.** For a Boolean function $f$, a coordinate set $J$, and a point $x$ of the sign cube, the absolute value of the coordinate projection of $f$ at $x$ is at most $1$.

**Proof.** The projection estimate bounds the absolute value of the projection of any function by that function’s product supremum norm (`abs_projectOnCoordinates_le_productSupNorm`). For the real-valued version of a Boolean function, the product supremum norm is $1$ (`productSupNorm_toReal_eq_one`). Applying the projection estimate to this real-valued function and substituting its norm gives the result.

**Key facts.** `FABL.productSupNorm_toReal_eq_one`, `FABL.abs_projectOnCoordinates_le_productSupNorm`.
