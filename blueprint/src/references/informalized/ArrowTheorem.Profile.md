<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: Profile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A profile of voter orderings

**Definition.** `Profile (n : ℕ) := Fin n → Fin 6`, an `abbrev`.

A profile assigns to each of the `n` voters one of the six transitive strict
orderings of `{a, b, c}` (indexed by `Fin 6` as in `abPref` / `bcPref` /
`caPref`). This is the sample space of Kalai's argument: "voters draw i.i.d.
uniform orderings" is realized as the uniform measure on `Profile n`, and every
expectation in the file is written as `(1/6 : ℝ)^n * ∑ p : Profile n, …`.

**Remark.** Being an `abbrev` (reducible) rather than a `def` is load-bearing,
not cosmetic: instance search must see through `Profile n` to `Fin n → Fin 6` to
find the `Fintype` instance that makes `∑ p : Profile n, …` and
`Finset.univ : Finset (Profile n)` typecheck. The one place this surfaces is the
cardinality step in `acyclic_implies_corrFunc`, where
`simp [Fintype.card_pi, Fintype.card_fin, …]` computes
`Fintype.card (Profile n) = 6^n` — the `6^n` that cancels the `(1/6)^n`
normalizer. No proof.

**Used in.** Pervasively: the domain of `abVotes`, `bcVotes`, `caVotes`, the
quantifier in `acyclic`, and the profile sums in `profile_kernel_gen`, the three
kernel lemmas, `expected_product_helper`, the three `expected_product_*` lemmas,
and `acyclic_implies_corrFunc`.
