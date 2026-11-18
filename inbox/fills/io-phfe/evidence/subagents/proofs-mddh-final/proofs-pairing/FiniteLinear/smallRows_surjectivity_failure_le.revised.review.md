# Revised SmallRows candidate

The exact live opening docstring and whole searched theorem header were compared byte-for-byte
against `Pairing/MatrixDH/FiniteLinear.lean`; they are unchanged. The draft contains one outer
tactic block, no new helper, and no admissions. No Lean/lake/Git command or live edit was run.

## Two changes requested by root

- The one-row branch composes `Matrix.mulVecLin M` with the EXISTING
  `LinearEquiv.funUnique (Fin 1) K K`. If that scalar functional is nonzero, the EXISTING
  `Module.Dual.range_eq_top_of_ne_zero` and `LinearMap.range_eq_top` give surjectivity.
  `Equiv.comp_surjective` transports it back to the row map. Its contrapositive yields the
  zero functional; `Matrix.mulVec_single_one` and `LinearEquiv.funUnique_apply` identify
  its zero coefficients. There is no division-based construction of a preimage.
- The singleton event uses EXISTING `TCSlib.Cryptography.OneWay.uprob_eq_one_div_card`.
  The only remaining calculation is the matrix-function type's cardinality. The two-row
  branch still uses `Matrix.card_GL_field`, not a new counting argument.

## Interfaces for native verification

The key elaboration boundary is the coercion of the local composite functional `L` to
`e.toEquiv ∘ Matrix.mulVec M`; these are definitionally the same. If explicit normalization
is needed, use the public `LinearMap.coe_comp`, `LinearEquiv.coe_toLinearMap`,
`LinearEquiv.coe_toEquiv`, and `Matrix.coe_mulVecLin` readers, rather than re-proving an
equivalence-composition lemma.

The final coefficient `change` only reads the public `funUnique_apply` result at the unique
Fin-1 coordinate. It does not unfold a TCSlib definition. All zero-row/two-row arithmetic
from the earlier candidate is retained and remains subject to root native checking.

No mathematical obstruction was found. This candidate is not yet claimed native-checked.
