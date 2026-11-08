<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/SmallSetExpansion.lean :: BooleanAnalysis.Hypercontractivity.volume_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform volume upper bound

**Claim.** Every set in the Boolean cube has uniform volume at most $1$.

**Proof.** Expanding the indicator and uniform expectation shows that the volume is the number of points in the set divided by the total number of cube points. The set’s cardinality is at most that of the whole cube, so this ratio is at most $1$.
