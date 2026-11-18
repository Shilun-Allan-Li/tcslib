# Follow-up reuse correction: one-row surjectivity and singleton mass

No proof or native check supplied in this invocation. This note supersedes the two affected
parts of the earlier unvalidated smallRows candidate; root is already repairing them.

1. Singleton mass must use the EXISTING
   `TCSlib.Cryptography.OneWay.uprob_eq_one_div_card (0 : Matrix (Fin 1) (Fin 2) K)`
   at OneWayFunctions/Basic.lean:144. Then only normalize the existing matrix-function
   cardinality to q^2. Re-reading uprob_def/card_subtype would duplicate that public fact.
   MatrixDH/Diagonal.lean:109-113 already shows the exact probability-reader composition.

2. The existing functional-surjectivity result DOES cover the one-row hbad argument.
   Its exact namespace at Dual/Lemmas.lean:710 is
   `Module.Dual.range_eq_top_of_ne_zero`, not `LinearMap.range_eq_top_of_ne_zero`.
   The theorem's own body uses the even more direct public `LinearMap.surjective hf`.
   Therefore the explicit division-based preimage argument should be replaced.

Use e=`LinearEquiv.funUnique (Fin 1) K K` (LinearAlgebra/Pi.lean:576), with
`funUnique_apply` at583, and L=e.toLinearMap.comp (Matrix.mulVecLin M).
This L is a scalar-valued functional in Module.Dual K (Fin 2 -> K). If L != 0,
Module.Dual.range_eq_top_of_ne_zero and LinearMap.range_eq_top give its surjectivity.
Equiv.comp_surjective at Logic/Equiv/Defs.lean:338 transports that surjectivity
back through e.toEquiv to Matrix.mulVec M, using Matrix.coe_mulVecLin or
Matrix.mulVecLin_apply (ToLin.lean:274/277) to read the action.

Conversely, a failure of the row map to be surjective forces L=0. Evaluating this
functional equality at Pi.single j 1, then using Matrix.mulVec_single_one and the
funUnique application reader, gives M 0 j=0. Fin 1 subsingleton identifies every
row with 0; Matrix.ext yields M=0. This last coordinate argument only identifies
the matrix coefficients of a ZERO linear form; it no longer re-proves the public
claim that a NONZERO scalar-valued linear form is surjective.

An alternative is to establish L!=0 from M!=0 using those same single-coordinate
readers and apply the public surjectivity theorem contrapositively. Either route
uses the existing range theorem exactly. No new generic row-surjectivity helper
needs to be proved unless root's native searches expose an interface gap.
