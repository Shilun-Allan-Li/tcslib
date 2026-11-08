<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.expect_graphMatchingEdgeFourierFactor_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a Matching Fourier Factor

**Claim.** For a function whose nonzero Fourier coefficients are supported on sets of size $k$, the expected squared matching Fourier factor is at most $\frac{k!}{n^k}$ times the total squared Fourier weight at level $k$.

**Proof.** First replace the expectation over labels on matching edges by the equal expectation over maps from the $k$ positions to the label set, using the matching-factor expectation identity (`FABL.expect_graphMatchingEdgeFourierFactor_sq_eq`). The resulting quantity is the expected square of the Fourier coefficient indexed by the image of such a map. The bound for label tuples of a function whose Fourier support is concentrated at level $k$ (`FABL.expect_labelTuple_fourierCoeff_sq_le`) bounds this expectation by $\frac{k!}{n^k}$ times the squared Fourier weight at level $k$, as required.

**Key facts.** `FABL.expect_graphMatchingEdgeFourierFactor_sq_eq`, `FABL.expect_labelTuple_fourierCoeff_sq_le`.
