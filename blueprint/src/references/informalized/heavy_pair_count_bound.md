<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/Decomposition.lean :: heavy_pair_count_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Heavy Pair Count Bound

**Claim.** For a 3-uniform hypergraph $H$, the number of pairs of degree greater than $d$, multiplied by $d$, is at most three times the number of hyperedges.

**Proof.** Sum the degrees over the heavy pairs. Each such pair has integer degree greater than $d$, hence degree at least $d+1$; consequently this sum is at least $d$ times the number of heavy pairs. The sum over heavy pairs is at most the sum of degrees over all two-element subsets of the vertex set. Recount this latter sum by hyperedges: a pair contributes once for each hyperedge containing it, so the total is $\sum_{C\in H}\binom{|C|}{2}$. Every hyperedge has size $3$, and therefore contributes $\binom{3}{2}=3$. The total is $3|H|$, giving the claimed inequality.
