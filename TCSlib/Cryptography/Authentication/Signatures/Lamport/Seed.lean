/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.TableCoins
import Mathlib.Data.List.OfFn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A fair planting bit and a uniform Lamport table

## Main definitions

* `seedCoins`: a seed of `1 + 2n²` bits is a fair bit paired with a Lamport preimage table.

## Main results

* `seedCoins_apply` and `seedCoins_symm`: forward and inverse equations.
* `ofFn_seedCoins_symm`: the inverse seed word is `c :: secretWord T`.
* `ofFn_seedCoins`: the seed word decomposes into its planting bit and table serialization.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 137.2. This is generic seed serialization glue for its reduction.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

/-- The seed width `1 + 2n²` is the successor width `2n² + 1`. -/
theorem seedCoins_width (n : ℕ) : 1 + 2 * n * n = 2 * n * n + 1 :=
  Nat.add_comm _ _

/-- A seed of `1 + 2n²` bits is equivalent to a Boolean planting bit and a typed key table.
The bit is the first seed entry and the table occupies the remaining entries in row order. -/
def seedCoins (n : ℕ) : (Fin (1 + 2 * n * n) → Bool) ≃ Bool × Table n :=
  ((Equiv.arrowCongr (finCongr (seedCoins_width n)) (Equiv.refl Bool)).trans
    (Fin.consEquiv (fun _ : Fin (2 * n * n + 1) => Bool)).symm).trans
      ((Equiv.refl Bool).prodCongr (tableCoins n))

/-- `seedCoins n x` consists of the first entry of `x` and the table represented by its
remaining entries, after the equality cast to successor width. -/
theorem seedCoins_apply (n : ℕ) (x : Fin (1 + 2 * n * n) → Bool) :
    seedCoins n x =
      (((Equiv.arrowCongr (finCongr (seedCoins_width n)) (Equiv.refl Bool)) x) 0,
        tableCoins n
          (Fin.tail ((Equiv.arrowCongr (finCongr (seedCoins_width n))
            (Equiv.refl Bool)) x))) := rfl

/-- The inverse seed equivalence prepends `c` to the coin tape represented by `T`, and casts
back from successor width to `1 + 2n²`. -/
theorem seedCoins_symm (n : ℕ) (c : Bool) (T : Table n) :
    (seedCoins n).symm (c, T) =
      (Equiv.arrowCongr (finCongr (seedCoins_width n).symm) (Equiv.refl Bool))
        (Fin.cons c ((tableCoins n).symm T)) := rfl

/-- The inverse seed word is the planting bit followed by the serialized key table:
`List.ofFn ((seedCoins n).symm (c,T)) = c :: secretWord T`. -/
theorem ofFn_seedCoins_symm {n : ℕ} (c : Bool) (T : Table n) :
    List.ofFn ((seedCoins n).symm (c, T)) = c :: secretWord T := by
  rw [seedCoins_symm, ofFn_arrowCongr_finCongr, List.ofFn_cons, ofFn_tableCoins_symm]

/-- Every seed word is its extracted planting bit followed by its extracted key table's
serialization. -/
theorem ofFn_seedCoins {n : ℕ} (x : Fin (1 + 2 * n * n) → Bool) :
    List.ofFn x = (seedCoins n x).1 :: secretWord (seedCoins n x).2 := by
  have h := ofFn_seedCoins_symm (seedCoins n x).1 (seedCoins n x).2
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using h

end TCSlib.Cryptography.Authentication.LamportFill
