import TCSlib.Complexity.BranchingPrograms.Barrington

/-! Probe P2 (commutator, Lemma 3).  Kernel `decide` only.
* program order (Mathlib product): `sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1 = c[0,2,1,4,3]`
  (Bar89's (13254)), written `List.formPerm [0,2,1,4,3]`;
* the right-to-left reading of Bar89's word `(12345)(13542)(54321)(24531)` as a Mathlib product
  gives `c[0,3,2,4,1]` (Bar89's (14352));
* `IsFiveCycle` of `sigma1`, `sigma2` and the commutator (the statements of C9). -/

open BranchingProgram Equiv

example : sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1 = (List.formPerm [0, 2, 1, 4, 3] : Perm (Fin 5)) := by
  decide

example : sigma1 * sigma2 * sigma1⁻¹ * sigma2⁻¹ = (List.formPerm [0, 3, 2, 4, 1] : Perm (Fin 5)) := by
  decide

-- the two readings differ
example : sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1 ≠ sigma1 * sigma2 * sigma1⁻¹ * sigma2⁻¹ := by
  decide

-- the C9 statements, by kernel decide
example : IsFiveCycle sigma1 := by decide
example : IsFiveCycle sigma2 := by decide
example : IsFiveCycle (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) := by decide +kernel
example : IsFiveCycle (sigma1 * sigma2 * sigma1⁻¹ * sigma2⁻¹) := by decide
-- and a non-five-cycle is rejected
example : ¬ IsFiveCycle (Equiv.swap 0 1) := by decide
example : ¬ IsFiveCycle 1 := by decide

#eval (List.finRange 5).map (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1)
