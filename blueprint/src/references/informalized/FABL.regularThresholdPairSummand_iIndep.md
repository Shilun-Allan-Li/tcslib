<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.regularThresholdPairSummand_iIndep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of Pair Summands

**Claim.** Under the correlated-pair distribution, the two-dimensional summands indexed by the coordinates are mutually independent.

**Proof.** First regard the data as a function on the finite product of coordinate-pair spaces, equipped with the product measure whose common coordinate law is the correlated sign-pair law. Each summand is then a function of just its own coordinate pair. The coordinate projections on a product measure are independent, and applying a measurable function separately to each projection preserves independence; here measurability follows because the spaces are finite. To transfer this independence to the original pair of sign vectors, reindex that pair as a function of coordinate pairs. The correlated-pair distribution pushes forward under this reindexing to the independent product of the coordinate correlated-pair laws (`FABL.correlatedPairPMF_map_pairCoordinatesEquiv`), and the measure of that product law is the corresponding product measure (`FABL.independentProductPMF_toMeasure`). Thus the coordinate summands on the original space are the pullbacks of the independent coordinate functions, so they too are mutually independent.

**Key facts.** `FABL.correlatedPairPMF_map_pairCoordinatesEquiv`, `FABL.independentProductPMF_toMeasure`.
