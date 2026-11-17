<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.length_filter_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting a predicate on an initial interval

**Claim.** The number of indices $j<n$ satisfying $q(j)$ equals the count of numbers below $n$ satisfying $q$.

**Proof.** By definition, the count of a predicate below $n$ is the number of elements in the initial interval $[0,n)$ satisfying it. The list `List.range n` enumerates precisely those indices, so filtering this list by $q$ and taking its length gives that count.
