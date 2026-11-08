<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.uniformInner_projection_self_le_expect_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection self-inner-product bound

**Claim.** The uniform inner product of a coordinate projection with itself is at most the uniform average of its absolute value.

**Proof.** Express the inner product as the uniform average of the pointwise square. The projection has absolute value at most $1$ (\texttt{FABL.abs_booleanCoordinateProjection_le_one}). Therefore, for each value $t$ of the projection, $t^2=|t|^2\le |t|$, since $0\le |t|\le1$. Averaging this pointwise inequality gives the claimed bound.

**Key facts.** `FABL.abs_booleanCoordinateProjection_le_one`.
