<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/StatisticalDistance.lean :: TCSlib.InformationTheory.statDist_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Statistical Distance

**Claim.** For distributions $p$ and $q$ on a finite set, their statistical distance is nonnegative.

**Proof.** Each term $|p(a)-q(a)|$ in the defining sum is nonnegative. The sum is therefore nonnegative, and multiplying it by $1/2\ge0$ preserves that inequality.
