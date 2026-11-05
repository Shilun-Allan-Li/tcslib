<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: max_influence_lower_bound -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.86) -->

# Some coordinate carries at least the average influence

**Claim.** For any `f : BooleanFunc n` with `0 < n`, there is a coordinate
`i : Fin n` with `totalInfluence f / n ≤ influence i f`. Since
`totalInfluence f = ∑ i, influence i f`, this is the averaging (pigeonhole)
statement that the maximum individual influence is at least the mean.

**Proof.** By contradiction (`by_contra`, `push_neg`): assume
`hlt : ∀ i, influence i f < totalInfluence f / n`.

1. `hsum : totalInfluence f = ∑ i, influence i f` holds by `rfl` (definition of
   `totalInfluence`).
2. Sum the strict bounds over the nonempty index type
   (`Finset.sum_lt_sum_of_nonempty`, nonemptiness from
   `Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)`):
   `∑ i, influence i f < ∑ i, totalInfluence f / n`.
3. The right-hand constant sum is `n * (totalInfluence f / n)`
   (`Finset.sum_const`, `nsmul_eq_mul`), which is `totalInfluence f` since
   `n ≠ 0` (`field_simp`).
4. Chaining gives `totalInfluence f < totalInfluence f`, contradicting
   `lt_irrefl`. ∎

**Remark.** `hn : 0 < n` is used twice — for nonemptiness of the index set in
step 2 and to cancel `n` in step 3.
