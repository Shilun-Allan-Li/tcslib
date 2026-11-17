<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.expectedComparisons_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear bound on expected comparisons

**Claim.** For every rank $k$ and finite list $l$, the expected number of comparisons made by the randomized selection procedure is at most $10|l|$.

**Proof.** If the list is empty, the procedure makes no comparisons. Otherwise, write $n=|l|$. The expected-comparison recurrence expresses the expectation as the average over the $n$ pivot positions of $n$ plus the expected cost of the recursive subproblem, if there is one (`Randomized.expectedComparisons_eq`). Inductively, each recursive expectation is at most ten times the length of its filtered list. For a pivot $x$, that recursive length is bounded by $\max(\#\{y\in l:y<x\},\#\{y\in l:x<y\})$; this also bounds the zero-cost branch. Hence the sum of the unweighted bounds over all pivot positions is at most $n^2+10\sum_{x\in l}\max(\#\{y<x\},\#\{y>x\})$. The counting estimate that four times this latter sum is at most $3n^2$ (`Randomized.four_mul_sum_max_countP_le`) makes the total at most $n^2+(30/4)n^2\le 10n^2$. Dividing by $n$, as prescribed by the recurrence, gives the bound $10n$.

**Key facts.** `Randomized.expectedComparisons_eq`, `Randomized.four_mul_sum_max_countP_le`.
