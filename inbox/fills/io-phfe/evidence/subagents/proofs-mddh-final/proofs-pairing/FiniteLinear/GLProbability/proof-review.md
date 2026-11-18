# Shared GL-count probability proof candidate

Exact CORRECTED target copied from root's MatrixUnitProbabilityExact.run2.lean.txt,
changing only anonymous example to the intended theorem name. The entire subtraction
is parenthesized inside the product binder; the first draft's malformed product must
NOT be reused. Opening prose/sketch retained. One outer tactic block, no admissions,
no new helper/import/runtime definition, and no Lean/lake/Git command or live edit.

## Native search status, accurately bounded

Root reports evidence/search/matrix-unit-probability/run2:
- exact?%: corrected header clean; only the expected cannot-close search error.
- apply?: many unrelated partial equality wrappers, then 800000-heartbeat exhaustion.
  This is NOT an exhaustive no-match search and is not claimed as one.
Run1 had an invalid unparenthesized product header and is not valid reuse evidence.
Root explicitly authorized this one proof block despite the bounded apply search.

## Exact reuse

The probability bridge and uprob_def expose uniform event mass. The IsUnit predicate
subtype is definitionally the range of Units.val (the same reading used in the existing
smallRows square branch), so no new subtype equivalence or cardinality proof is built.
Nat.card_range_of_injective Units.val_injective reduces its cardinality to the EXISTING
Matrix.card_GL_field theorem. The only remaining denominator calculation reuses
Fintype.card_fun/card_fin, Nat.cast_pow, and pow_mul. No invertibility/rank counting,
cardinality theorem, sampler, or probability law is reproved.

The product remains a natural count cast to Real; natural subtraction is never silently
replaced with real subtraction. The proof does not need n>0 and covers the empty matrix
case uniformly. The existing ambient matrix Nonempty instance is supplied by zero, so
there is no extra inhabitedness assumption or custom instance.

Native verification remains pending. Once this shared helper passes, root can remove
the duplicated local unit-range/card_GL/ambient-cardinality steps from smallRows and
use the same helper at n=3 after simulator tape reindexing. No mathematical obstruction.
