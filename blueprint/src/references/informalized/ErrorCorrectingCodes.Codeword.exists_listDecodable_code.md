<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/ListDecoding.lean :: exists_listDecodable_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Existence of list-decodable codes by counting

**Claim.** Fix `n`, `1 ≤ L < M ≤ q^n` with `q = Fintype.card α`, and `p : ℝ`
with `0 ≤ p ≤ 1`. Suppose `V` bounds every Hamming ball,
`(hamming_ball ⌊p*n⌋₊ y).card ≤ V` for all `y`, and the counting inequality
`q^n · C(V, L+1) · C(q^n - (L+1), M - (L+1)) < C(q^n, M)` holds. Then some code
`C : Code n α` has `C.card = M` and is `(p, L)`-list-decodable.

**Proof.** `contrapose h_ineq`: assume no `M`-element subset is
`(p, L)`-list-decodable and derive the reverse inequality by counting bad
subsets inside `Finset.powersetCard M univ`.

1. `h_bad_codes`: for a fixed centre `y`, the `M`-subsets `C` with
   `|ball(y) ∩ C| ≥ L + 1` number at most
   `|powersetCard (L+1) (ball y)| · C(q^n - (L+1), M - (L+1))`. Each such `C`
   splits as `S ∪ (C \ S)` for some `(L+1)`-subset `S` of the ball
   (`Finset.exists_subset_card_eq`), so the family injects into a
   `Finset.biUnion` of images `fun T => S ∪ T` over
   `powersetCard (M - (L+1)) (univ \ S)`; `Finset.card_le_card`,
   `card_biUnion_le`, `card_image_le`, `card_powersetCard`, `card_sdiff` give
   the bound, then `Nat.choose_le_choose` with `hV y` replaces `|ball y|` by
   `V`.
2. `h_bad_codes_count`: union-bound over centres. The `M`-subsets bad for
   *some* `y` sit inside the `biUnion` over `y : Codeword n α`
   (`Finset.card_le_card`, `Finset.card_biUnion_le`), so summing step 1 over
   all `q^n` centres (`Finset.sum_le_sum`, `Fintype.card_pi`) bounds them by
   `q^n · C(V, L+1) · C(q^n - (L+1), M - (L+1))`.
3. By the contrapositive hypothesis every `M`-subset is bad, so the filter is
   all of `powersetCard M univ` (`Finset.filter_true_of_mem` after unfolding
   `list_decodable`), whose cardinality is `C(q^n, M)`
   (`simp [Finset.card_univ]`). Chaining with step 2 contradicts `h_ineq`. ∎

**Used in.** `list_decoding_capacity` (hypothesis supplied by
`listDecoding_counting_ineq`).
