<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.identDistrib_of_independent_coordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Joint laws from independent coordinate laws

**Claim.** If two finite families are each independent and corresponding coordinates have identical distributions, then their random vectors have identical distributions.

**Proof.** The coordinate maps into the finite-dimensional real product are measurable up to null sets because each corresponding pair has identical distributions. Independence identifies the law of each random vector with the product of its coordinate laws. Since the coordinate laws agree one by one, these product measures agree, so the vector laws are identical.

**Caveat.** The supplied proof uses the product-law characterization of independence and the coordinatewise map-equality field of each identical-distribution hypothesis. The only listed upstream item, the Rademacher-law identity, is not used by this proof and does not provide those facts.
