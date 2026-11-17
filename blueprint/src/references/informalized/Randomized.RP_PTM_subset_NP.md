<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.RP_PTM_subset_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Sided Time Lies in NP

**Claim.** Every language decidable in polynomial time by a one-sided randomized machine with member acceptance probability at least $2/3$ belongs to NP.

**Proof.** Rewrite NP as the union of nondeterministic time classes (Complexity.NP_eq_iUnion_NTIME). Under this characterization, it suffices to map each polynomial-time one-sided randomized time class into the nondeterministic time class with the corresponding bound. The established inclusion from randomized time to nondeterministic time does exactly this (Randomized.RTIME_subset_NTIME), and applying it across the union proves the result.

**Key facts.** `Complexity.NP_eq_iUnion_NTIME`, `Randomized.RTIME_subset_NTIME`.
