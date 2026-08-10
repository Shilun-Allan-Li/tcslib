<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: natCast_one_lt_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An alphabet size at least two exceeds one as a real

**Claim.** For `q : ℕ` with `2 ≤ q`, the cast satisfies `(1 : ℝ) < q`.

**Proof.** One line: `exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hq`.

- `Nat.lt_of_lt_of_le one_lt_two hq` chains `1 < 2` with `2 ≤ q` to get `1 < q`
  in `ℕ`.
- `exact_mod_cast` moves the strict inequality across the `ℕ → ℝ` coercion.

Granular helper. It is the strict-inequality companion to
`natCast_pos_of_two_le`, and it is the form actually needed to know that
`Real.logb q` is strictly monotone (base greater than one) rather than merely
well-defined.

**Used in.** `Entropy.lean` (`hq1`, `hq_1`) and `ListDecoding.lean`; also the
sole input to the three `Basic.lean` lemmas
`natCast_sub_one_nonneg_of_two_le`, `natCast_sub_one_pos_of_two_le`, and
`natCast_ne_one_of_two_le`, each of which calls it through a `show ... from`
term inside `linarith`.
