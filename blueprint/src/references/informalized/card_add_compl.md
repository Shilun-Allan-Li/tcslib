<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: card_add_compl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A coordinate set and its complement partition the `n` coordinates

**Claim.** For every `M : Finset (Fin n)`, `M.card + (E_c M).card = n`.

**Proof.** Two steps.

1. `unfold E_c; simp [Finset.card_compl]` rewrites the goal to
   `M.card + (Fintype.card (Fin n) - M.card) = n`, i.e. to
   `M.card + (n - M.card) = n` over ℕ.
2. `Nat.add_sub_of_le` closes it, given `M.card ≤ n` — obtained from
   `Finset.card_le_univ` composed with `Fintype.card (Fin n) = n`
   (`norm_num`).

**Remark.** Truncated ℕ subtraction is why step 2 needs the `M.card ≤ n` side
condition at all. The lemma is currently **unused**: `cleaning_dimension_identity`,
the natural consumer, inlines the same `Finset.card_compl` computation itself.
