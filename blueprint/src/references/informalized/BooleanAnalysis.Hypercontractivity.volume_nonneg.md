<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.volume_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative uniform volume

**Claim.** Every set in the Boolean cube has nonnegative uniform volume.

**Proof.** The volume is the uniform weight times the sum of the set indicator over all cube points. The uniform weight is nonnegative, and every indicator value is nonnegative (BooleanAnalysis.Hypercontractivity.setIndicator_nonneg), so their product and hence the volume are nonnegative.

**Key facts.** `BooleanAnalysis.Hypercontractivity.setIndicator_nonneg`.
