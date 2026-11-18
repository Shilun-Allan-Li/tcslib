# hBasis local fill

Proof-only replacement for the hBasis term sorry in the root-native-PASS ladder.
Exactly one tactic block, no new helper/import/definition, no admission. No live source
edit or Lean/lake/Git command was run. hCount remains unchanged and admitted.

The symmetry of the EXISTING basisMatrix_eq reader is exactly the goal after ordinary
definitional reduction of the local e/ac/row compositions and the existing Mathlib
Equiv constructors. prodAssoc groups A,c without touching Tail; arrowProd, per-row
prodComm+snocEquiv, and piComm produce the reader's displayed snoc/transpose lambda.

Rule 10: basisMatrix is read ONLY through basisMatrix_eq, never supplied as a definition
body to simp/rw/unfold. No public definition is supplied to any tactic. The only reduction
needed is local definitions and Core/Mathlib equivalence application; there is no new
generic bijection or coordinate proof, nor a TCSlib-definitional-closure shortcut.

Static source reads: current live LinearSimulator hBasis header and unchanged row/ac/e
local definitions, basisMatrix_eq, Mathlib Fin.snocEquiv/arrowProdEquivProdArrow/
piCongrRight/piComm/prodAssoc. The full ladder already passed native with the original
local holes, but this fill remains subject to root's native check. No mathematical
obstruction was found.
