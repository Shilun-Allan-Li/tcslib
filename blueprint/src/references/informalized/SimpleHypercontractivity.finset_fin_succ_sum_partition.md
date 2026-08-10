<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: finset_fin_succ_sum_partition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Summing over subsets of [n+1] by membership of the last element

**Claim.** For any `φ : Finset (Fin (n + 1)) → ℝ`,
`∑ S : Finset (Fin (n+1)), φ S =
 ∑ T : Finset (Fin n), φ (T.image Fin.castSucc) +
 ∑ T : Finset (Fin n), φ (T.image Fin.castSucc ∪ {Fin.last n})`.
Every subset of `Fin (n+1)` either avoids `Fin.last n` — and is then the lift of a
unique `T : Finset (Fin n)` — or contains it, and is that lift with `Fin.last n`
adjoined.

**Proof.**

1. `h_partition`: `Finset.univ` equals the union of the two images
   `T ↦ T.image castSucc` and `T ↦ T.image castSucc ∪ {Fin.last n}` over
   `univ : Finset (Finset (Fin n))`. Shown by `ext S` and
   `by_cases h : Fin.last n ∈ S`; in both branches the witness is
   `T = univ.filter (fun i => Fin.castSucc i ∈ S)`, and the set equality is
   finished by `Finset.ext_iff`-style membership reasoning (`Fin.lastCases` /
   `Fin.ext_iff` to handle `i = Fin.last n`, plus `aesop`).
2. `rw [h_partition, Finset.sum_union]` splits the sum; disjointness comes from
   `Finset.disjoint_right` — a member of the first image cannot contain
   `Fin.last n`, extracted by `Finset.ext_iff.mp H (Fin.last n)`.
3. `Finset.sum_image` twice reindexes each image sum back to a sum over
   `T : Finset (Fin n)`. Both injectivity obligations are the same argument:
   given `T.image castSucc = T'.image castSucc`, specialize the `Finset.ext_iff`
   equality at `Fin.castSucc a` and conclude `a ∈ T ↔ a ∈ T'`. ∎

**Used in.** `noiseOp_snoc` — the Fourier sum over `Finset (Fin (n+1))` is split
this way, the two halves becoming the `avgLast` and `diffLast` terms (via
`chiS_snoc_castSucc` / `chiS_snoc_with_last` and the two `card_image_*` lemmas).
