<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: count_bad_S -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# At most a `2^{-ℓ}` fraction of seeds are bad (nonzero input)

**Claim.** Fix `v : Fin width → ZMod p` with `v ≠ 0`. Among the seeds
`S : Fin ℓ → Finset (Fin width)`, the number for which the randomized OR-approximator is
wrong satisfies

`#{S | approxOr_val p v S ≠ OR_val p v} * 2 ^ ℓ ≤ Fintype.card (Fin ℓ → Finset (Fin width))`.

**Proof.**

1. `simp [approxOr_failure_iff, hv]` replaces the failure condition by its combinatorial
   form: `S` is bad iff `∑ i ∈ S k, v i = 0` for *every* `k`.
2. `htuple` : the bad seeds factor as a product, `#{S | ∀ k, P (S k)} = (#{T | P T}) ^ ℓ`
   for `P T := (∑ i ∈ T, v i = 0)`. Proved by the explicit equivalence
   `{S // ∀ k, P (S k)} ≃ (Fin ℓ → {T // P T})` together with `Fintype.card_congr`,
   `Fintype.card_fun`, `Fintype.card_fin`, and `Fintype.card_subtype` to convert between
   filter cardinalities and subtype cards.
3. `rw [← Nat.mul_pow]` turns the goal into `(#{T | ∑ i ∈ T, v i = 0} * 2) ^ ℓ ≤ (2 ^ width) ^ ℓ`,
   so it suffices to prove the `ℓ = 1` case.
4. `hmain` : `#{T | ∑ i ∈ T, v i = 0} * 2 ≤ 2 ^ width`, by a toggle involution. Pick `t`
   with `v t ≠ 0` and set `toggle_t T := if t ∈ T then T.erase t else insert t T`.
   - `h_toggle_t_invol` : it is an involution (`Finset.insert_erase`, `Finset.erase_insert`).
   - `lem_toggle_sum` : summing the indicator of `∑ i ∈ T, v i = 0` over all `T` is
     unchanged by precomposing with `toggle_t`, via `Equiv.sum_comp` for the permutation
     built from the involution.
   - `lem_pair` : for each `T`, `indicator T + indicator (toggle_t T) ≤ 1` — if both sums
     vanished then `Finset.sum_erase_add` (or `Finset.sum_insert`) would force `v t = 0`.
   - Adding the two equal sums and bounding termwise by `1` gives `∑ T, 1 = 2 ^ width`.
5. `Nat.pow_le_pow_left hmain ℓ` raises step 4 to the `ℓ`-th power.

**Remark.** Only the `ℓ = 1` case carries content; the `ℓ` seeds are independent, so the
failure probability halves per seed. The `v ≠ 0` hypothesis is what supplies the toggle
coordinate `t`.

**Used in.** `count_bad_S_or`, which removes the `v ≠ 0` hypothesis.
