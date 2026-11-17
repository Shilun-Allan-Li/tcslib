<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_polyHeads_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial machine head bounds

**Claim.** Under any of the stated stage-dependent head-position bounds, every head position lies between $-1$ and $q$, inclusive.

**Proof.** Split according to the control stage. In the absent-state case, the hypothesis already gives both inequalities. In a loop stage, every position is nonnegative and at most $q$. In a rewind stage, every position is at least $-1$ and strictly below $q$, hence at most $q$. In an advance or emit stage, positions are nonnegative and strictly below $q$, which also implies the required bounds. Copy and setup stages cannot occur under the hypothesis, since their corresponding head condition is false.
