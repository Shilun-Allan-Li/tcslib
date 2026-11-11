/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Ring.Nat

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The parameter recovered by Levin padding

The padded family recovers a parameter from every input length by taking the largest natural number whose fixed power fits within that length. The public equations and bounds are the interface for the machine proof.

## Main definitions

* `TCSlib.Cryptography.PadQuad.nu` is the recovered parameter.

## Main results

* `nu_pow_le`, `nu_le`, `lt_succ_nu_pow` and `le_nu` characterize its bounds.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010. (§2.13, Lemma 64.3.)
-/

namespace TCSlib.Cryptography.PadQuad

/-- The parameter recovered from the input length `m`: the largest `n ≤ m` with `n^d ≤ m`
(`ν m = ⌊m^{1/d}⌋`). -/
def nu (d m : ℕ) : ℕ := Nat.findGreatest (fun n => n ^ d ≤ m) m

/-- The recovered parameter is the greatest bounded natural number whose
degree-d power fits within the input length. -/
theorem nu_eq (d m : ℕ) : nu d m = Nat.findGreatest (fun n => n ^ d ≤ m) m := rfl

/-- `ν(m)^d ≤ m`. -/
theorem nu_pow_le {d : ℕ} (hd : 1 ≤ d) (m : ℕ) : nu d m ^ d ≤ m :=
  Nat.findGreatest_spec (P := fun n => n ^ d ≤ m) (Nat.zero_le m)
    (by show 0 ^ d ≤ m; rw [Nat.zero_pow hd]; exact Nat.zero_le m)

/-- `ν(m) ≤ m`. -/
theorem nu_le (d m : ℕ) : nu d m ≤ m := Nat.findGreatest_le m

/-- `m < (ν(m) + 1)^d`: the recovered parameter is maximal. -/
theorem lt_succ_nu_pow {d : ℕ} (hd : 1 ≤ d) (m : ℕ) : m < (nu d m + 1) ^ d := by
  by_cases h : nu d m < m
  · have := Nat.findGreatest_is_greatest (P := fun n => n ^ d ≤ m) (n := m) (k := nu d m + 1)
      (Nat.lt_succ_self _) (by omega)
    exact not_le.mp this
  · have hm : nu d m = m := le_antisymm (nu_le d m) (not_lt.mp h)
    rw [hm]
    exact lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_self_pow (by omega) _)

/-- `n ≤ ν(m)` whenever `n^d ≤ m`. -/
theorem le_nu {d : ℕ} (hd : 1 ≤ d) {n m : ℕ} (h : n ^ d ≤ m) : n ≤ nu d m :=
  Nat.le_findGreatest ((Nat.le_self_pow (by omega) n).trans h) h

end TCSlib.Cryptography.PadQuad
