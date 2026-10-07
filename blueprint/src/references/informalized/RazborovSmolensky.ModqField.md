<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: ModqField -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The standard field for the `MOD q` lower bound

**Definition.** For a prime `p` and a natural `q`, `ModqField p q` is the `abbrev`
`GaloisField p (q - 1)`, i.e. the finite field `𝔽_(p^(q-1))`. It is the ambient field in
which the Razborov–Smolensky argument for `MOD q` is carried out.

**Remark.** The exponent `q - 1` is chosen so that a primitive `q`-th root of unity exists:
for `q` prime and `p ≠ q`, the unit group has order `p ^ (q - 1) - 1`, which is divisible by
`q` by Fermat's little theorem.

**Used in.** `natCard_modqField` (`Nat.card (ModqField p q) = p ^ (q - 1)`, via
`GaloisField.card` with the side condition `q_sub_one_ne_zero`),
`exists_unit_of_order_q_modqField` (a unit of order exactly `q`), and the root-of-unity
existence statement `∃ ω : ModqField p q, ω ^ q = 1 ∧ ω ≠ 1`.
