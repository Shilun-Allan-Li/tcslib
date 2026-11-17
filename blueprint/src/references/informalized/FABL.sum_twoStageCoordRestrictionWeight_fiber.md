<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.sum_twoStageCoordRestrictionWeight_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Stage Restriction Weight on a Fiber

**Claim.** For a fixed coordinatewise restriction assignment, summing the two-stage weights over all pairs of assignments that compose to it gives the weight of that assignment at parameter $\delta_1\delta_2$.

**Proof.** For each coordinate, collect the pairs of restrictions whose composition equals the target restriction at that coordinate. The global fiber of assignments is exactly the product of these coordinatewise fibers, since composition is defined coordinate by coordinate. Rewrite the sum over the fiber as a sum over this product, with the weight expressed as the product of its coordinate weights. The finite-product sum identity factors this into a product, one factor per coordinate, of the local sums over pairs composing to that coordinate's target. Each such local sum equals the target restriction's weight at parameter $\delta_1\delta_2$ (`FABL.sum_twoStageCoordRestrictionWeight_localFiber`). The resulting product is the weight of the fixed assignment at that parameter, by definition.

**Key facts.** `FABL.sum_twoStageCoordRestrictionWeight_localFiber`.
