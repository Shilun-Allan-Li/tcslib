<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: card_filter_add_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deleting `u` and `−u` costs at most two elements

**Claim.** Let `V` be an additive group, `S : Finset V` and `u : V`. Then
`S.card ≤ (S.filter (fun v => v ≠ u ∧ v ≠ -u)).card + 2`. The hypothesis
`u ∈ S` is present but unused (it is named `_hu`), so the bound holds for any
`u`.

**Proof.**

1. It suffices to show the complementary filter is small:
   `(S.filter (fun v => ¬(v ≠ u ∧ v ≠ -u))).card ≤ 2`, since
   `Finset.filter_card_add_filter_neg_card_eq_card` splits `S.card` into the
   two filters and `omega` closes the arithmetic.
2. That complementary filter is contained in `{u, -u}`: unfolding membership
   with `Finset.mem_filter`, `not_and_or` and `not_ne_iff` leaves
   `v = u ∨ v = -u`, discharged by `tauto`.
3. Chaining `Finset.card_le_card` with `Finset.card_insert_le` bounds
   `|{u, -u}|` by `2`.

**Used in.** The inductive step of `rankin_bound_general`: after picking a unit
vector `u ∈ S`, the induction is run on `T = S.filter (v ≠ u ∧ v ≠ -u)`, and
this lemma is the "Step 1" accounting that recovers `S.card` from `T.card`.
