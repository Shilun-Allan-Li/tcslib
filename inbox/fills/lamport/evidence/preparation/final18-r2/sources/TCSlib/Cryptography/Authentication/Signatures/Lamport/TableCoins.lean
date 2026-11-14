/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted
import TCSlib.Cryptography.Asymptotic.OneWay
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lamport coin tapes as typed key tables

## Main definitions

* `tableCoins`: regroup a `2n²`-bit tape as the false and true `n`-bit preimages in each row.

## Main results

* `tableCoins_apply` and `tableCoins_symm`: the forward and inverse block equations.
* `ofFn_tableCoins_symm`: the inverse equivalence serializes a table as `secretWord`.
* `secretWord_tableCoins`: serializing the table of a tape recovers the tape's word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 137.1 and Theorem 137.2. This module is generic serialization glue for the
  protocol's preimage table.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

/-- The row-major tape width `n(2n)` equals the generator width `2n²`. -/
theorem tableCoins_width (n : ℕ) : 2 * n * n = n * (2 * n) := by ring

/-- A `2n²`-bit coin tape is equivalent to a table with an `n`-bit cell for each
`(i,c) ∈ Fin n × Bool`. The first cell of each row is indexed by `false`, the second by
`true`. Zero-width tapes and empty tables are included. -/
def tableCoins (n : ℕ) : (Fin (2 * n * n) → Bool) ≃ Table n :=
  ((((Equiv.arrowCongr (finCongr (tableCoins_width n)) (Equiv.refl Bool)).trans
      (FunFamily.blocks n (2 * n))).trans
      (Equiv.piCongrRight fun _ : Fin n =>
        (FunFamily.blocks 2 n).trans
          (Equiv.arrowCongr finTwoEquiv (Equiv.refl (Fin n → Bool))))).trans
      (Equiv.curry (Fin n) Bool (Fin n → Bool)).symm)

/-- The cell `(i,c)` of `tableCoins n x` is block `c` of the `i`th two-preimage row
of `x`, with `false` selecting block zero and `true` block one. -/
theorem tableCoins_apply (n : ℕ) (x : Fin (2 * n * n) → Bool) (i : Fin n) (c : Bool) :
    tableCoins n x (i, c) =
      FunFamily.blocks 2 n
        (FunFamily.blocks n (2 * n)
          ((Equiv.arrowCongr (finCongr (tableCoins_width n)) (Equiv.refl Bool)) x) i)
        (finTwoEquiv.symm c) := rfl

/-- The inverse of `tableCoins` concatenates the two preimage cells of each row and then
concatenates the rows, casting only between the equal widths `n(2n)` and `2n²`. -/
theorem tableCoins_symm (n : ℕ) (T : Table n) :
    (tableCoins n).symm T =
      (Equiv.arrowCongr (finCongr (tableCoins_width n).symm) (Equiv.refl Bool))
        ((FunFamily.blocks n (2 * n)).symm fun i =>
          (FunFamily.blocks 2 n).symm fun j => T (i, finTwoEquiv j)) := rfl

/-- The word of the inverse tape is exactly the row-major secret word:
`List.ofFn ((tableCoins n).symm T) = secretWord T`.

**Proof sketch.** Reading the width cast preserves the word. The block-equivalence inverse
concatenates the words of its rows. Inside each row, the two-block inverse concatenates the
false and true preimages, which is the published serialization equation for `secretWord`. -/
theorem ofFn_tableCoins_symm {n : ℕ} (T : Table n) :
    List.ofFn ((tableCoins n).symm T) = secretWord T := by
  rw [tableCoins_symm, ofFn_arrowCongr_finCongr, FunFamily.ofFn_blocks_symm, secretWord_eq]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [FunFamily.ofFn_blocks_symm, OneWay.flatten_ofFn_two]
  rfl

/-- Serializing the table obtained from a tape recovers the tape's word:
`secretWord (tableCoins n x) = List.ofFn x`. -/
theorem secretWord_tableCoins {n : ℕ} (x : Fin (2 * n * n) → Bool) :
    secretWord (tableCoins n x) = List.ofFn x := by
  rw [← ofFn_tableCoins_symm, Equiv.symm_apply_apply]

end TCSlib.Cryptography.Authentication.LamportFill
