/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.List.GetD

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian elimination over `ZMod p`: the determinant identities

Infrastructure for [AB09 §7.2.4] (the determinant of Lovász's test); not itself a result of the
book. A matrix over `ZMod p` is given by its rows, lists of natural numbers
(`Complexity.BinArith.matOfRows`). This file proves the three identities behind the
elimination loop of `TCSlib.Complexity.ClassP.BinaryArith.DetMod`: eliminating the first
column with a nonzero pivot in the first row, rotating the first row to the bottom, and a zero
first column.

## Main definitions

* `Complexity.BinArith.matOfRows` — the `m × m` matrix with entries `rows[i][j]` (default `0`).
* `Complexity.BinArith.elimRow` — the reduced row `row[1..] - (row[0]·a⁻¹)·pivot[1..]` mod `p`.

## Main results

* `Complexity.BinArith.det_matOfRows_elim` — `det M = a · det M'` for a pivot `a ≠ 0`.
* `Complexity.BinArith.det_matOfRows_rotate` — rotating the rows multiplies by `(-1)^(m-1)`.
* `Complexity.BinArith.det_matOfRows_eq_zero` — a zero first column gives `det M = 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.4.)
-/

namespace Complexity

namespace BinArith

/-- The `m × m` matrix over `ZMod p` whose `(i, j)` entry is `rows[i][j]` (missing entries
read as `0`). -/
def matOfRows (p m : ℕ) (R : List (List ℕ)) : Matrix (Fin m) (Fin m) (ZMod p) :=
  Matrix.of fun i j => (((R.getD i []).getD j 0 : ℕ) : ZMod p)

/-- The row of the Schur complement: with `f = row[0]·inv mod p`, the entries
`(row[j+1] + p - (f·pivot[j+1] mod p)) mod p`. -/
def elimRow (p inv : ℕ) (piv row : List ℕ) : List ℕ :=
  List.zipWith (fun r y => (r + p - (row.headD 0 * inv % p) * y % p) % p) row.tail piv.tail

/-- Entries of a tail. -/
theorem getD_tail (l : List ℕ) (j : ℕ) : l.tail.getD j 0 = l.getD (j + 1) 0 := by
  cases l <;> simp

/-- The head as an entry. -/
theorem getD_zero_eq_headD (l : List ℕ) : l.getD 0 0 = l.headD 0 := by
  cases l <;> simp

/-- Entries of a zipped list inside both lists. -/
theorem getD_zipWith (f : ℕ → ℕ → ℕ) (l₁ l₂ : List ℕ) (j : ℕ) (h₁ : j < l₁.length)
    (h₂ : j < l₂.length) : (List.zipWith f l₁ l₂).getD j 0 = f (l₁.getD j 0) (l₂.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h₁,
    List.getD_eq_getElem _ _ h₂, List.getElem_zipWith]

/-- In `ZMod p`, the reduced difference `(r + p - (x mod p)) mod p` is `r - x`. -/
theorem natCast_sub_mod {p : ℕ} (hp : 0 < p) (r x : ℕ) :
    (((r + p - x % p) % p : ℕ) : ZMod p) = r - x := by
  rw [ZMod.natCast_mod, Nat.cast_sub (by have := Nat.mod_lt x hp; omega), Nat.cast_add,
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

/-- Fermat: `a^(p-2) mod p` is the inverse of a nonzero `a` in `ZMod p`. -/
theorem natCast_pow_mod_eq_inv {p : ℕ} [Fact p.Prime] (a : ℕ) (ha : (a : ZMod p) ≠ 0) :
    ((a ^ (p - 2) % p : ℕ) : ZMod p) = (a : ZMod p)⁻¹ := by
  rw [ZMod.natCast_mod, Nat.cast_pow]
  apply eq_inv_of_mul_eq_one_left
  have h2 := (Fact.out : p.Prime).two_le
  rw [← pow_succ, show p - 2 + 1 = p - 1 by omega]
  exact ZMod.pow_card_sub_one_eq_one ha

/-- **Elimination with a pivot in the first row**: if the first entry `a` of the first row is
nonzero in `ZMod p` and `inv` represents `a⁻¹`, then
`det M = a · det M'` for the matrix `M'` of the reduced rows `elimRow`.

**Proof sketch.** Subtracting `(M i 0 / a)` times the first row from every other row keeps the
determinant (`Matrix.det_eq_of_forall_row_eq_smul_add_const`) and clears the first column
below the pivot; the Laplace expansion along that column
(`Matrix.det_succ_column_zero`) leaves `a` times the minor, which is `M'` entrywise
(`natCast_sub_mod`). -/
theorem det_matOfRows_elim {p : ℕ} [Fact p.Prime] (piv : List ℕ) (rs : List (List ℕ))
    (hpiv : piv.length = rs.length + 1) (hrs : ∀ r ∈ rs, r.length = rs.length + 1)
    (inv : ℕ) (ha : ((piv.headD 0 : ℕ) : ZMod p) ≠ 0)
    (hinv : (inv : ZMod p) = ((piv.headD 0 : ℕ) : ZMod p)⁻¹) :
    (matOfRows p (rs.length + 1) (piv :: rs)).det =
      ((piv.headD 0 : ℕ) : ZMod p) * (matOfRows p rs.length (rs.map (elimRow p inv piv))).det := by
  set M := matOfRows p (rs.length + 1) (piv :: rs)
  set a : ZMod p := ((piv.headD 0 : ℕ) : ZMod p)
  have hM0 : M 0 0 = a := by cases piv <;> simp [M, a, matOfRows]
  let c : Fin (rs.length + 1) → ZMod p := fun i => if i = 0 then 0 else M i 0 * a⁻¹
  let B : Matrix (Fin (rs.length + 1)) (Fin (rs.length + 1)) (ZMod p) :=
    Matrix.of fun i j => M i j - c i * M 0 j
  have hB : M.det = B.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c]) (fun i j => ?_)
    simp [B, c]
  rw [hB, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hcol : ∀ i : Fin rs.length, B i.succ 0 = 0 := by
    intro i
    simp only [B, c, Matrix.of_apply, Fin.succ_ne_zero, if_false, hM0]
    field_simp
    ring
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero]
  have hB00 : B 0 0 = a := by simp [B, c, hM0]
  rw [hB00]
  congr 1
  congr 1
  ext i j
  have hi : (i : ℕ) < rs.length := i.isLt
  have hrow := hrs (rs.getD i []) (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)
  have hmap : (rs.map (elimRow p inv piv)).getD i [] = elimRow p inv piv (rs.getD i []) := by
    rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getD_eq_getElem _ _ hi,
      List.getElem_map]
  simp only [B, c, Matrix.submatrix_apply, Matrix.of_apply, Fin.succ_ne_zero, if_false,
    M, matOfRows, Fin.val_succ, List.getD_cons_succ, Fin.val_zero, List.getD_cons_zero]
  rw [hmap]
  generalize rs.getD i [] = row at hrow ⊢
  have hj : (j : ℕ) < rs.length := j.isLt
  unfold elimRow
  rw [getD_zipWith _ _ _ _ (by simp; omega) (by simp; omega), getD_tail, getD_tail,
    natCast_sub_mod (Fact.out : p.Prime).pos]
  push_cast [ZMod.natCast_mod, hinv, getD_zero_eq_headD]
  ring

/-- **Rotating the rows**: moving the first row of an `(m+1)`-row matrix to the bottom
multiplies its determinant by `(-1)^m`.

**Proof sketch.** The rotated matrix is the original with rows permuted by `finRotate`
(row `i` of the rotation is row `i + 1` of the original, the last is the first), and
`Matrix.det_permute` with `sign_finRotate` gives the sign `(-1)^m`. -/
theorem det_matOfRows_rotate (p : ℕ) (r₀ : List ℕ) (rs : List (List ℕ)) :
    (matOfRows p (rs.length + 1) (rs ++ [r₀])).det =
      (-1) ^ rs.length * (matOfRows p (rs.length + 1) (r₀ :: rs)).det := by
  have h : matOfRows p (rs.length + 1) (rs ++ [r₀]) =
      (matOfRows p (rs.length + 1) (r₀ :: rs)).submatrix (finRotate (rs.length + 1)) id := by
    ext i j
    simp only [matOfRows, Matrix.submatrix_apply, Matrix.of_apply, id, finRotate_succ_apply]
    have hrow : (rs ++ [r₀]).getD i [] =
        (r₀ :: rs).getD ((i + 1 : Fin (rs.length + 1)) : ℕ) [] := by
      rcases Nat.lt_or_ge (i : ℕ) rs.length with hi | hi
      · have hlt : i < Fin.last rs.length := by rw [Fin.lt_iff_val_lt_val]; simpa using hi
        rw [List.getD_append _ _ _ _ hi, Fin.val_add_one_of_lt hlt, List.getD_cons_succ]
      · have hi' : (i : ℕ) = rs.length := by have := i.isLt; omega
        have hlast : i = Fin.last rs.length := Fin.ext hi'
        rw [List.getD_append_right _ _ _ _ (by omega), hlast, Fin.last_add_one]
        simp
    rw [hrow]
  rw [h, Matrix.det_permute, sign_finRotate]
  simp

/-- **A zero first column**: if every row of a matrix with at least one row starts with `0`
in `ZMod p`, its determinant is `0`. -/
theorem det_matOfRows_eq_zero (p m : ℕ) (R : List (List ℕ))
    (h : ∀ i < m + 1, (((R.getD i []).headD 0 : ℕ) : ZMod p) = 0) :
    (matOfRows p (m + 1) R).det = 0 :=
  Matrix.det_eq_zero_of_column_eq_zero 0 fun i => by
    simp only [matOfRows, Matrix.of_apply, Fin.val_zero, getD_zero_eq_headD]
    exact h i i.isLt

/-- Reducing every entry modulo `p` does not change the matrix over `ZMod p`. -/
theorem matOfRows_map_mod (p m : ℕ) (R : List (List ℕ)) :
    matOfRows p m (R.map (List.map (· % p))) = matOfRows p m R := by
  ext i j
  simp only [matOfRows, Matrix.of_apply]
  rw [show ([] : List ℕ) = List.map (· % p) [] from rfl, List.getD_map,
    show (0 : ℕ) = 0 % p from (Nat.zero_mod p).symm, List.getD_map, ZMod.natCast_mod]
  simp

/-- The `0 × 0` determinant is `1`. -/
theorem det_matOfRows_zero (p : ℕ) (R : List (List ℕ)) : (matOfRows p 0 R).det = 1 :=
  Matrix.det_fin_zero

end BinArith

end Complexity
