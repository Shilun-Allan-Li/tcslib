<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.sum_map_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum over an Initial Range

**Claim.** For a function from the natural numbers to a commutative additive monoid, the sum of its values on the list obtained by mapping $f$ over $\mathrm{range}(n)$ equals the sum over all $i<n$.

**Proof.** The two sides are definitionally the same finite sum: the list `List.range n` enumerates the natural numbers below $n$ in order, and the finite-set range sum uses that same enumeration. Hence the equality holds directly.
