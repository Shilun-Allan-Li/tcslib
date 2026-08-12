<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: subset_sum_zero_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# For a nonzero vector, at most half of all subsets sum to zero

**Claim.** For `v : Fin n → ZMod p` with `v ≠ 0`,

`2 * (univ.filter (fun s : Finset (Fin n) => ∑ i ∈ s, v i = 0)).card ≤ (univ : Finset (Finset (Fin n))).card`.

That is, the zero-subset-sum sets are at most half of all `2^n` subsets.

**Proof.** `obtain ⟨i, hi⟩ := Function.ne_iff.mp hv` fixes a coordinate with
`v i ≠ 0`.

1. **Toggle injection** (`h_pairs`, inner): the map
   `s ↦ if i ∈ s then s \ {i} else s ∪ {i}` sends every zero-sum subset to a
   nonzero-sum subset, since toggling `i` shifts the sum by `± v i ≠ 0`. Formally
   the zero-sum filter is `⊆ Finset.image (that map) (nonzero-sum filter)`,
   proved by `intro s hs; simp_all; use …; aesop`.
2. **Counting** (`h_pairs`, outer): `Finset.card_le_card` on that inclusion plus
   `Finset.card_image_le` gives
   `#{s | ∑ i ∈ s, v i = 0} ≤ #{s | ∑ i ∈ s, v i ≠ 0}` inside `powerset univ`.
3. **Complement**: `Finset.card_add_card_compl` applied to the zero-sum filter
   says the two counts add up to the total number of subsets; with
   `simp_all [Finset.filter_not, Finset.card_sdiff]` this and step 2 leave a
   linear inequality closed by `linarith`.

**Remark.** The statement is over `univ : Finset (Finset (Fin n))` while the
proof works inside `Finset.powerset univ`; `simp_all` identifies the two.

**Status.** Currently unused — no other declaration references it. The bound the
development actually consumes is the equivalent `hmain` proved inline inside
`count_bad_S`, via an involution `toggle_t` rather than an image bound.
