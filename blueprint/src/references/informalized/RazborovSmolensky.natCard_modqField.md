<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: natCard_modqField -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The standard field for the `MOD q` bound has `p ^ (q - 1)` elements

**Claim.** For primes `p`, `q`,

`Nat.card (ModqField p q) = p ^ (q - 1)`,

where `ModqField p q` is the abbreviation for `GaloisField p (q - 1)`.

**Proof.** Immediate from `GaloisField.card p (q - 1)`, whose `q - 1 ≠ 0` side
condition is supplied by `q_sub_one_ne_zero`; `simpa [ModqField]` unfolds the
abbreviation.

**Used in.** `exists_unit_of_order_q_modqField`, where it is converted to
`Fintype.card` form by `Nat.card_eq_fintype_card`.
