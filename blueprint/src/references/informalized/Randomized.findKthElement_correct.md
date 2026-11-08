<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.findKthElement_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of randomized selection

**Claim.** When $1\le k\le |l|$, every supported outcome of the randomized selection procedure returns an entry $y$ of $l$ with fewer than $k$ entries strictly below it and at least $k$ entries less than or equal to it.

**Proof.** Proceed by induction on the list length and condition on the chosen pivot $x$. The empty-list case is impossible under $k\le |l|$. If $k$ is at most the number of entries below $x$, the procedure recurses on the entries below $x$. The induction hypothesis supplies a returned entry $y<x$ of that filtered list with the required rank there. Because $y<x$, every entry of the original list counted below $y$, or at most $y$, is also below $x$; translating the filtered counts back to the original list therefore preserves both rank inequalities. If instead fewer than $k$ entries are at most $x$, the procedure recurses above $x$ with rank reduced by the number of entries at most $x$. The induction hypothesis gives a returned $y>x$ with that adjusted rank. The original counts below and at most $y$ each split into the corresponding count within the entries above $x$ and the entries at most $x$; adding back the latter count yields the required inequalities for $k$. In the remaining case, the number below $x$ is less than $k$ and the number at most $x$ is at least $k$, so returning $x$ itself has the stated property. The count decompositions used in the above-pivot case are `Randomized.countP_lt_eq_countP_filter_add` and `Randomized.countP_le_eq_countP_filter_add`; the partition of the list into entries above $x$ and entries at most $x$ is `Randomized.countP_lt_add_countP_le`.

**Key facts.** `Randomized.countP_lt_eq_countP_filter_add`, `Randomized.countP_le_eq_countP_filter_add`, `Randomized.countP_lt_add_countP_le`.
