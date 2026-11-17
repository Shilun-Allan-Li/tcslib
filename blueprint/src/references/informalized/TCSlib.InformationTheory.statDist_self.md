<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/StatisticalDistance.lean :: TCSlib.InformationTheory.statDist_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance from a Distribution to Itself

**Claim.** For any distribution $p$ on a finite set, its statistical distance from itself is zero.

**Proof.** For every outcome $a$, the difference $p(a)-p(a)$ is zero, so every absolute-value term in the defining sum vanishes. The statistical distance is consequently zero.
