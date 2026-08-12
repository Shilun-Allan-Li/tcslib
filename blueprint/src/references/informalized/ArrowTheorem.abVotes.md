<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: abVotes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The a-vs-b vote vector of a profile

**Definition.** For `p : Profile n`,

`abVotes p : BoolCube n := fun i => abPref (p i)`.

Voter `i` has ordering `p i`; reading off that ordering's a-vs-b ballot gives
coordinate `i`. So `abVotes p` is the `n`-bit input one feeds to the social
welfare function to ask "does society prefer `a` to `b` under profile `p`?",
and `f (abVotes p)` is the answer in `±1`.

**Remark.** Pure post-composition, `abPref ∘ p` — no proof, and no lemmas are
stated about it. Its role is to be the first of three parallel projections of a
single profile: `abVotes`, `bcVotes`, `caVotes` extract the three pairwise
comparisons from the *same* `p`, which is exactly the coupling that creates the
`-1/3` correlation. Independent draws would give correlation `0` and the whole
argument would collapse.

**Used in.** `acyclic` (the forbidden patterns are stated at `f (abVotes p)`),
the kernel lemmas `profile_inner_product_kernel` and `profile_kernel_abca`
(where it is passed as the `votes1` argument of `profile_kernel_gen`),
`expected_product_eq_corrFunc`, `expected_product_abca`, and
`acyclic_implies_corrFunc`.
