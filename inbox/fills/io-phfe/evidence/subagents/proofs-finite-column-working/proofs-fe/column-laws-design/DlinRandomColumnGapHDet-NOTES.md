# Random-column hDet local proof candidate

Status: isolated proof-only scratch fragment, NOT natively checked. No Lean/lake/build/Git,
live-source edit, process operation, extra agent or native probe was run by this child.

Fragment: DlinRandomColumnGapHDet.proof.lean.inc. Exactly one tactic block, `by` followed by
four-space body for replacement of the existing local hDet term sorry. No new helper,
algorithm, admission or public statement is introduced. The main header/prose is untouched.
The original random skeleton is unchanged; hCoords/hBadMass remain term sorries there.

Exact target, in the existing skeleton context:
  hDet : forall (ab rs : Fin 2 -> K) (t : K),
    (C ab rs t).det = ab 0 * ab 1 * (t - rs 0 - rs 1)
where local C is precisely the three rows
  (a,0,a*r), (0,b,b*s), (1,1,t).

## Reuse / actual static checks

Read the exact local C/hDet in DlinRandomColumnGap.skeleton.lean.inc:29-50. Searched current
live ColumnLaws and this scratch directory for hDet/det_fin_three/C, then read the existing
Mathlib determinant formula in LinearAlgebra/Matrix/Determinant/Basic.lean:811-824.
The fragment invokes that theorem directly; it does NOT re-prove determinant expansion.

Read the exact entry readers in Data/Fin/VecNotation.lean:
cons_val_zero :122, cons_val_one :234, cons_val_two :237, head_cons :190, tail_cons :194;
and Matrix.of_apply in LinearAlgebra/Matrix/Defs.lean:83. These are the only matrix-entry
readers supplied to simp. C is this proof's own local let and may be read directly.

After det_fin_three and the public finite-entry/zero/unit readers, the remaining identity
is a*b*t - a*(b*s) - (a*r)*b = a*b*(t-r-s), discharged by ring over the existing Field K.
No nonzero diagonal, finite-cardinality or characteristic restriction is used. No new
probability/counting routine or group scalar extraction is involved, and the canonical
random-law loss is unchanged. No dlinMatrixSlack term is added.

The seven-line fragment has one by token, no placeholder/admission, and no >100-column line.
Native elaboration / Rule 10 validation remains root-owned and pending. Filling this one
local block does not establish the random law: hCoords and hBadMass are still outstanding.
