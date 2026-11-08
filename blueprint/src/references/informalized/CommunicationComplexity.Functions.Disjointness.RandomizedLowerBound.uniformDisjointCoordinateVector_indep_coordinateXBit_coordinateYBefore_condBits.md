<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_indep_coordinateXBit_coordinateYBefore_condBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional independence of residual bits

**Claim.** After conditioning on any value of Alice's conditioning bit vector, Alice's bit at $i$ and Bob's earlier-bit vector are independent.

**Proof.** The event that Alice's conditioning vector equals a fixed bit vector is the intersection, over coordinates, of the events fixing the individual conditioning bits (`coordinateAliceCondBits_fiber_eq_iInter`). Consider at each coordinate the pair consisting of its conditioning bit and its residual bit. These pairs are mutually independent under the original law, by `uniformDisjointCoordinateVector_residual_cond_iIndepFun`. Conditioning on the specified value of each conditioning bit preserves mutual independence of the residual bits: each conditioning event has positive probability (`uniformDisjointCoordinateVector_measure_condBit_ne_zero`), so the conditional-independence theorem for independent coordinate pairs applies. In particular, the residual at coordinate $i$ is independent of the collection of residuals at coordinates $k<i$; the two index sets are disjoint. Finally, the residual at $i$ is Alice's bit $X_i$, while the residuals before $i$, assembled into a vector and set to zero thereafter, give Bob's earlier-bit vector. Independence is preserved under these measurable recodings, proving the assertion.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateAliceCondBits_fiber_eq_iInter`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_residual_cond_iIndepFun`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_measure_condBit_ne_zero`.
