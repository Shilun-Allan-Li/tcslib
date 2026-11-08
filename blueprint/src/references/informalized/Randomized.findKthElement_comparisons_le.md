<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.findKthElement_comparisons_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Worst-case comparison bound

**Claim.** Every supported outcome $(a,c)$ of the randomized selection procedure on a list $l$ satisfies $2c\le |l|(|l|+1)$.

**Proof.** Proceed by induction on the list length, following the procedure's pivot choice. If the list is empty, its sole possible outcome has zero comparisons. Otherwise, choose a pivot $x$. If the procedure recurses, every supported result comes from a supported result on the corresponding filtered list, and the current step adds $|l|$ comparisons. Each filter removes at least the pivot itself, so its length $m$ satisfies $m+1\le |l|$. The induction bound gives twice the recursive comparison count at most $m(m+1)$; adding $2|l|$ is at most $|l|(|l|+1)$ by $m+1\le |l|$. If the procedure returns the pivot, it uses exactly $|l|$ comparisons, which directly satisfies the same bound. The support of a mixture and of a mapped distribution reduces these cases to the corresponding recursive or immediate outcomes, respectively.
