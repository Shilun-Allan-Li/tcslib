<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: card_filter_numFree_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Counting restrictions with exactly `k` free variables

**Claim.** For all `n k : ℕ`, the number of `ρ : Restriction n` (i.e.
`Fin n → Option Bool`) with `ρ.numFree = k` is `n.choose k * 2 ^ (n - k)`.

**Proof.** Partition by the free-variable set, then count each fiber.

1. `ρ.numFree = k` is by definition `ρ.freeVars.card = k`, so the filter is
   rewritten with `rfl`.
2. **Fiber count** (`hcard`): for a fixed `S : Finset (Fin n)`, the restrictions
   with `ρ.freeVars = S` are exactly the image of
   `φ g = fun i => if i ∈ S then none else some (g i)` over the `g : Fin n → Bool`
   that vanish on `S` (`himg`, proved by `ext` in both directions). `φ` is
   injective on that set (`hφinj`), so `Finset.card_image_of_injOn` applies, and a
   second bijection `ψ : (↥Sᶜ → Bool) → (Fin n → Bool)` (injective, with range
   exactly that set) gives the count `Fintype.card (↥Sᶜ → Bool) = 2 ^ (n - S.card)`.
3. **Partition** (`hpart`): the filter `ρ.freeVars.card = k` is the disjoint
   `Finset.biUnion` over `S ∈ (univ : Finset (Fin n)).powersetCard k` of the
   fibers `ρ.freeVars = S`; disjointness holds because `ρ.freeVars` determines `S`.
4. `Finset.card_biUnion` plus step 2 makes every summand `2 ^ (n - k)` (using
   `S.card = k` from `Finset.mem_powersetCard`), so `Finset.sum_const` and
   `Finset.card_powersetCard` give `n.choose k * 2 ^ (n - k)`.

**Used in.** `bad_count_bound` (the fiber-summation step of the switching lemma),
where the number of encoding targets `γ` with `γ.numFree = s - d` is needed;
it is also the `numSRestrictions` count. `private` helper.
