<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: bcVotes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The b-vs-c vote vector of a profile

**Definition.** For `p : Profile n`,

`bcVotes p : BoolCube n := fun i => bcPref (p i)`.

Coordinate `i` is voter `i`'s b-vs-c ballot, read off that voter's ordering
`p i`. Then `f (bcVotes p)` is society's verdict on `b` versus `c` under the
profile `p`. Pure post-composition `bcPref ∘ p`; no proof.

**Remark.** The middle of the three projections of a profile. It appears on both
sides of the argument — as the second slot of the ab–bc pair and the first slot
of the bc–ca pair — which is why the file needs both
`profile_inner_product_kernel` and `profile_kernel_bcca` rather than one lemma
plus symmetry.

**Used in.** `acyclic`, the kernel lemmas `profile_inner_product_kernel` (as
`votes2`) and `profile_kernel_bcca` (as `votes1`),
`expected_product_eq_corrFunc`, `expected_product_bcca`, and
`acyclic_implies_corrFunc`.
