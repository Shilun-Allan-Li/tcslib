<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.expCost_pure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected cost of a point mass

**Claim.** For any pair $(b,n)$, the expected second coordinate under the point-mass distribution concentrated at $(b,n)$ is $n$.

**Proof.** The point mass assigns probability one to $(b,n)$ and zero to every other pair. Thus the expectation sum has only one nonzero contribution, namely $1\cdot n=n$.
