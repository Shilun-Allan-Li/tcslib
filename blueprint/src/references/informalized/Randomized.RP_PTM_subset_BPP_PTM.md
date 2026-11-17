<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.RP_PTM_subset_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Sided Time Lies in Bounded-Error Time

**Claim.** Every language decidable in polynomial time by a one-sided randomized machine with member acceptance probability at least $2/3$ is decidable in polynomial time with correct-answer probability at least $2/3$ on every input.

**Proof.** Write the one-sided polynomial-time class as a union over polynomial exponents. For each exponent, the inclusion from one-sided randomized time to bounded-error randomized time at the same time bound is already established (Randomized.RTIME_subset_BPTIME). Applying this inclusion to every member of the union proves the desired class inclusion.

**Key facts.** `Randomized.RTIME_subset_BPTIME`.
