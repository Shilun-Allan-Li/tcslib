<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli.lean :: fixedSizeRestrs_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Counting the restrictions with exactly `k` free variables

**Claim.** For `k ≤ n`, `(fixedSizeRestrs n k).card = numSRestrictions n k`, i.e.
the number of restrictions `ρ : Fin n → Option Bool` with exactly `k` starred
coordinates is `C(n,k) · 2^(n−k)`.

**Proof.** The work is in one inner `have h_card`, which counts the same family
described as a filter on `Fin n → Option Bool` by the number of `none`s.

1. A single `have h_count` rewrites that filter as a `Finset.biUnion` over
   `Finset.powersetCard k univ`: for each candidate star-set `s`, the block is the
   image of `({i : Fin n // i ∉ s} → Bool)` under
   `f ↦ fun i => if i ∈ s then none else some (f ⟨i, _⟩)`. Proven by `ext ρ` and
   `simp [Finset.mem_biUnion, Finset.mem_image]`; the forward direction supplies
   `s := univ.filter (ρ · = none)` and recovers the off-`s` bits with `Option.get`
   (`generalize_proofs`, `grind`), the backward direction is `simp [ha]`.
2. `Finset.card_biUnion` applies: distinct star-sets give disjoint blocks
   (`Finset.disjoint_left`, then `contrapose!` and compare coordinates).
3. Each block has card `2 ^ (n − s.card)` by `Finset.card_image_of_injective`
   (injectivity from `congr_fun`) plus `Finset.card_univ` for the function type on
   the complement subtype.
4. Every `s ∈ powersetCard k univ` has `s.card = k` (`Finset.mem_powersetCard`),
   so the sum collapses to `(powersetCard k univ).card * 2^(n−k) = C(n,k)·2^(n−k)`.

Finally `convert h_card` transports the count from raw functions to
`Restriction n`, via `Finset.card_image_of_injective` on the identity coercion,
and `ext; simp [fixedSizeRestrs]` / `simp [Restriction.freeVars]` matches
`(ρ i).isNone` against `ρ i = none`.

**Used in.** `switching_fixedSize_bound_small`, where it clears the denominator of
`fixedSizeRestrProb` so the counting switching lemma's ratio bound applies. Note
the hypothesis `hk : k ≤ n` is never used in the proof (the identity holds for all
`k`, both sides being `0` when `k > n`).
