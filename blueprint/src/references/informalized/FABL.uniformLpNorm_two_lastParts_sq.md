<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniformLpNorm_two_lastParts_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Norm of the Last-Coordinate Parts

**Claim.** For a real-valued function $f$ on the $(n+1)$-dimensional sign cube, its squared uniform $L^2$ norm is the sum of the squared uniform $L^2$ norms of its even and odd parts in the last coordinate.

**Proof.** Replace each squared norm by the uniform average of the corresponding square using `uniformLpNorm_two_sq_eq_expect_sq`. Decompose the average over the $(n+1)$-dimensional cube into an average over the first $n$ coordinates followed by an average over the last sign (`expect_snoc`). For each fixed first-coordinate point, the reconstruction identity `lastCoordinate_reconstruct` expresses the two possible values of $f$ as its even part plus or minus its odd part. Averaging their squares cancels the mixed terms and leaves the square of the even part plus the square of the odd part. Averaging this equality over the first $n$ coordinates, and distributing the average over the sum, yields the stated identity.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`, `FABL.expect_snoc`, `FABL.lastCoordinate_reconstruct`.
