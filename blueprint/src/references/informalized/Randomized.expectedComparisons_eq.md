<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.expectedComparisons_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected comparison recurrence

**Claim.** For a nonempty list, the expected number of comparisons equals the average over its pivot positions of the list length plus the expected cost of the recursive call selected by that pivot, with no recursive cost when the pivot is the answer.

**Proof.** Choose a pivot position uniformly from the $|l|$ positions. Conditional on that position, the procedure either recurses on the entries strictly below the pivot, recurses on the entries strictly above it with the adjusted rank, or returns the pivot immediately. In either recursive case, it has already made $|l|$ comparisons, so the conditional expected cost is $|l|$ plus the expected recursive cost; in the immediate-return case it is just $|l|$. The expectation of a mixture is the sum, over pivot positions, of each conditional expectation weighted by its probability $1/|l|$. The expectation decomposes across this mixture (`Randomized.expCost_bind`); adding the already-paid list length shifts expected cost by that amount (`Randomized.expCost_map_add`), and the point mass at the returned pivot has cost exactly $|l|$ (`Randomized.expCost_pure`).

**Key facts.** `Randomized.expCost_bind`, `Randomized.expCost_map_add`, `Randomized.expCost_pure`.
