<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: caVotes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The c-vs-a vote vector of a profile

**Definition.** For `p : Profile n`,

`caVotes p : BoolCube n := fun i => caPref (p i)`.

Coordinate `i` is voter `i`'s c-vs-a ballot under ordering `p i`, so
`f (caVotes p)` is society's verdict on `c` versus `a`. Pure post-composition
`caPref ∘ p`; no proof.

**Remark.** The closing comparison of the cycle, and the one carrying the
reversed orientation inherited from `caPref` (`true` = prefers `a`). With the
triple `(f (abVotes p), f (bcVotes p), f (caVotes p))` so oriented, "all three
equal `1`" reads as `a > b`, `b > c`, `c > a` — a genuine Condorcet cycle — which
is what `acyclic` rules out.

**Used in.** `acyclic`, the kernel lemmas `profile_kernel_bcca` and
`profile_kernel_abca` (both as `votes2`), `expected_product_bcca`,
`expected_product_abca`, and `acyclic_implies_corrFunc`.
