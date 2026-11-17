<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.signed_intersection_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Intersection Cancellation

**Claim.** If $S$ is not contained in $J$, then the alternating sum over subsets $T$ of $S$, weighted by $g(T\cap J)$, vanishes.

**Proof.** Choose an element $i\in S\setminus J$. Pair each subset of $S\setminus\{i\}$ with the subset obtained by inserting $i$. Their intersections with $J$ are identical because $i\notin J$, while their signs are opposite: inserting $i$ increases the subset size by one and reverses the parity of $|S|-|T|$. Thus every pair contributes zero, and the whole sum vanishes.
