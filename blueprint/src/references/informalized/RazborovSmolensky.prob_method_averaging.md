<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: prob_method_averaging -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Averaging over seeds: one seed that is bad for few points

**Claim.** Let `α`, `β` be finite with `β` nonempty, let `Bad : Finset α`, let
`Fail : α → β → Prop` be decidable, and let `C : ℕ`. If every `a ∈ Bad` fails for
few `b`, i.e. `(univ.filter (Fail a ·)).card * C ≤ Fintype.card β`, then some
single `b : β` satisfies

`(univ.filter (fun a => a ∈ Bad ∧ Fail a b)).card * C ≤ Bad.card`.

**Proof.** `by_contra! h`: assume every `b` violates the conclusion, so over `ℕ`
each `b` gives `Bad.card + 1 ≤ #{a | a ∈ Bad ∧ Fail a b} * C`.

1. **Double counting** (`h_sum`): `∑ b, #{a | a ∈ Bad ∧ Fail a b} = ∑ a ∈ Bad, #{b | Fail a b}`.
   `simp only [card_filter]` turns each card into a sum of indicators,
   `Finset.sum_comm` swaps the two sums, and
   `rw [← Finset.sum_subset (Finset.subset_univ Bad)] <;> aesop` restricts the
   outer sum from `univ` to `Bad` (the dropped terms vanish).
2. **Lower bound**: `Finset.sum_le_sum fun b _ => Nat.mul_le_mul_right C (h b)`
   sums the contradiction hypothesis over all `b`; `simp_all [← Finset.sum_mul _ _ _]`
   and `cases C <;> aesop` package it as
   `Fintype.card β * (Bad.card + 1) ≤ (∑ a ∈ Bad, #{b | Fail a b}) * C`.
3. **Upper bound**: the same quantity is at most `Fintype.card β * Bad.card`, by
   `Finset.sum_mul` to distribute `C` and `Finset.sum_le_sum fun a ha => h_prob a ha`
   termwise (`simpa [mul_comm]`).
4. Steps 2 and 3 give `|β| * (|Bad| + 1) ≤ |β| * |Bad|`, impossible since
   `Fintype.card_pos_iff.mpr ‹_›` makes `|β| > 0`; `nlinarith` closes it.

**Status.** Currently unused — no other declaration in the repository references
it. The seed-counting arguments that were built later (`count_bad_S`,
`pi_exists_bad_card_mul_le`) carry their own bounds instead of averaging.
