/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RelabelGarbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RowFromCoins

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The tape-to-seed coin relabeling bridge

The seed function is a parameter, specified by its key, nonce and shift-bit
readers. Relabeling its complete tape agrees with the generic seed relabeling.
Assignment XOR is extended to four row codes by the existing finite-embedding
permutation extension, which fixes unused codes. Unused key and shift positions
are padded with false masks.

## Main definitions

* `assignmentEmbedding`, `assignmentPerm`: assignment folds and their extended XOR permutation.
* `keyMask`, `rowPerm`, `shiftMask`: the padded coordinate actions on complete tapes.

## Main results

* `seed_relabel`: the seed of the relabeled tape is the relabeling of the original seed.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the coin relabeling).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel

open BoolCircuit TCSlib.Cryptography

/-- The binary fold of an assignment to at most two argument positions is below four.
This uses the published first-two-bit formula. [PS10, Protocol 162.6] -/
theorem assignmentFold_lt_four {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 4 := by
  rw [RowFromCoins.assignmentFold_eq_two a hl]
  have h₀ := Bool.toNat_le ((List.ofFn a).getD 0 false)
  have h₁ := Bool.toNat_le ((List.ofFn a).getD 1 false)
  omega

/-- For `l ≤ 2`, the assignment fold is below the exact code count `2^l`.
Thus unused codes begin at one for arity zero and at two for arity one. -/
theorem assignmentFold_lt_pow {l : ℕ} (a : Fin l → Bool) (hl : l ≤ 2) :
    (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 2 ^ l := by
  have hc : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · rw [RowFromCoins.assignmentFold_eq_two a (by decide),
      List.getD_eq_default (List.ofFn a) false (n := 0) (by rw [List.length_ofFn]),
      List.getD_eq_default (List.ofFn a) false (n := 1) (by rw [List.length_ofFn]; omega)]
    decide
  · rw [RowFromCoins.assignmentFold_eq_two a (by decide),
      List.getD_eq_default (List.ofFn a) false (n := 1) (by rw [List.length_ofFn])]
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    exact Bool.toNat_lt _
  · exact assignmentFold_lt_four a (by decide)

/-- For at most two positions, equal assignment folds imply equal assignments.

**Proof sketch.** The published two-bit formula writes each fold as `b₀ + 2 b₁`.
The bounds `b₀,b₁ ≤ 1` uniquely recover both natural-valued bits. Testing each
bit value for equality with one recovers the Boolean bits. Every valid position
is zero or one, so the public `ofFn` element readers recover the whole assignment. -/
theorem assignmentFold_injective (l : ℕ) (hl : l ≤ 2) :
    Function.Injective (fun a : Fin l → Bool =>
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) := by
  intro a b hab
  change (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 =
    (List.ofFn b).foldr (fun b k => b.toNat + 2 * k) 0 at hab
  rw [RowFromCoins.assignmentFold_eq_two a hl, RowFromCoins.assignmentFold_eq_two b hl] at hab
  -- Recover both binary digits from the weighted sum.
  have ha₀ := Bool.toNat_le ((List.ofFn a).getD 0 false)
  have ha₁ := Bool.toNat_le ((List.ofFn a).getD 1 false)
  have hb₀ := Bool.toNat_le ((List.ofFn b).getD 0 false)
  have hb₁ := Bool.toNat_le ((List.ofFn b).getD 1 false)
  have h₀ : ((List.ofFn a).getD 0 false).toNat = ((List.ofFn b).getD 0 false).toNat := by
    omega
  have h₁ : ((List.ofFn a).getD 1 false).toNat = ((List.ofFn b).getD 1 false).toNat := by
    omega
  have h₀' : (List.ofFn a).getD 0 false = (List.ofFn b).getD 0 false := by
    simpa only [Bool.toNat_eq_one, Bool.decide_eq_true] using
      congrArg (fun q : ℕ => decide (q = 1)) h₀
  have h₁' : (List.ofFn a).getD 1 false = (List.ofFn b).getD 1 false := by
    simpa only [Bool.toNat_eq_one, Bool.decide_eq_true] using
      congrArg (fun q : ℕ => decide (q = 1)) h₁
  -- Every assignment position is one of the recovered two digits.
  funext t
  have ht : (t : ℕ) = 0 ∨ (t : ℕ) = 1 := by have := t.isLt; omega
  have hget : (List.ofFn a).getD t false = (List.ofFn b).getD t false := by
    rcases ht with ht | ht
    · simpa only [ht] using h₀'
    · simpa only [ht] using h₁'
  rw [List.getD_eq_getElem (List.ofFn a) false (n := (t : ℕ)) (by rw [List.length_ofFn]; exact t.isLt),
    List.getD_eq_getElem (List.ofFn b) false (n := (t : ℕ)) (by rw [List.length_ofFn]; exact t.isLt),
    List.getElem_ofFn, List.getElem_ofFn] at hget
  exact hget

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel
