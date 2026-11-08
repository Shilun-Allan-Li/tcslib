<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.maxExpectedComparisons_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Comparisons for Selection

**Claim.** For every linearly ordered type and natural number $n$, the supremum of the expected number of comparisons made by randomized selection over all ranks and all input lists of length $n$ is at most $10n$.

**Proof.** The expected-comparisons bound holds for each rank and each input list: it is at most ten times that list's length (`Randomized.expectedComparisons_le`). Taking the supremum only over lists whose length is $n$ therefore bounds every term by $10n$, and hence bounds the supremum by $10n$.

**Key facts.** `Randomized.expectedComparisons_le`.
