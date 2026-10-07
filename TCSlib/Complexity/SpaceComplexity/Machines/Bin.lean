/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary counters as words

Register-tape programs keep counters in little-endian binary, as the words `Nat.bits n`
(least significant bit first, no redundant zeros). This file collects the word-level facts the
counter machines need: the value of a word, injectivity of `Nat.bits`, the carry rule of
the increment (`Complexity.LogProg.bits_succ`), and length bounds.

## Main definitions

* `Complexity.LogProg.bitsVal` — the value of a little-endian word.
* `Complexity.LogProg.incW` — the increment of a little-endian word (carry propagation).

## Main results

* `Complexity.LogProg.bitsVal_bits`, `Complexity.LogProg.bits_injective`.
* `Complexity.LogProg.bits_succ` — `Nat.bits (n + 1) = incW (Nat.bits n)`.
* `Complexity.LogProg.length_bits_le` — `|Nat.bits n| ≤ m` when `n < 2^m`;
  `Complexity.LogProg.length_bits_mono` — `|Nat.bits n|` is monotone in `n`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: counters in logarithmic space.)
-/

namespace Complexity.LogProg

/-- The value of a little-endian binary word. (Duplicates `BoolCircuit.bitsVal` of
`TCSlib.Complexity.CircuitComplexity.Adder`; to be unified.) -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * bitsVal w

/-- The increment of a little-endian binary word: flip the leading `1`s to `0` and the
first `0` (or the end) to `1`. -/
def incW : List Bool → List Bool
  | [] => [true]
  | false :: w => true :: w
  | true :: w => false :: incW w

/-- `Nat.bits` of an even and an odd number. -/
lemma bits_two_mul_add (n : ℕ) (b : Bool) (h : n = 0 → b = true) :
    Nat.bits (2 * n + b.toNat) = b :: Nat.bits n := by
  cases b with
  | false =>
    have hn : n ≠ 0 := fun h0 => by simpa using h h0
    simpa using Nat.bit0_bits n hn
  | true => simp

/-- The value of `Nat.bits n` is `n`. -/
lemma bitsVal_bits (n : ℕ) : bitsVal (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [bitsVal, Nat.zero_bits]
    · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
      have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by
        intro h0; simp; omega
      rw [hdecomp, bits_two_mul_add _ _ hb]
      simp only [bitsVal]
      rw [ih (n / 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]; omega

/-- `Nat.bits` is injective. -/
lemma bits_injective : Function.Injective Nat.bits := fun a b h => by
  rw [← bitsVal_bits a, ← bitsVal_bits b, h]

/-- **The carry rule**: the binary word of `n + 1` is the increment of that of `n`. -/
lemma bits_succ (n : ℕ) : Nat.bits (n + 1) = incW (Nat.bits n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.zero_bits, Nat.one_bits, incW]
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · -- `n = 2m`, `m ≠ 0`
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
        have hm : m ≠ 0 := by omega
        rw [Nat.bit0_bits m hm, show 2 * m + 1 = 2 * m + (true).toNat by rfl,
          bits_two_mul_add m true (fun _ => rfl)]
        rfl
      · -- `n = 2m + 1`
        obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
        rw [Nat.bit1_bits, show 2 * m + 1 + 1 = 2 * (m + 1) + (false).toNat by simp; ring,
          bits_two_mul_add (m + 1) false (by omega), ih m (by omega)]
        rfl

/-- The binary word of `n` has at most `m` letters when `n < 2^m`. -/
lemma length_bits_le {n m : ℕ} (h : n < 2 ^ m) : (Nat.bits n).length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

/-- Binary words of larger numbers are not shorter. -/
lemma length_bits_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

/-- The binary word of `n` has at most `⌊log₂ n⌋ + 1` letters. -/
lemma length_bits_le_log (n : ℕ) : (Nat.bits n).length ≤ Nat.log 2 n + 1 :=
  length_bits_le (Nat.lt_pow_succ_log_self (by norm_num) n)

/-- Every letter of `Nat.bits n` is followed by more letters or is a `1`: the word has no
trailing `0`. (The last letter is `true`.) -/
lemma bits_getLast (n : ℕ) (h : Nat.bits n ≠ []) : (Nat.bits n).getLast h = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Nat.zero_bits] at h
    · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
        rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
      have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by
        intro h0; simp; omega
      have e := bits_two_mul_add (n / 2) _ hb
      rw [← hdecomp] at e
      simp only [e]
      by_cases h0 : Nat.bits (n / 2) = []
      · simp only [h0, List.getLast_singleton]
        have : n / 2 = 0 := by
          have := bitsVal_bits (n / 2); rw [h0] at this; simp [bitsVal] at this; omega
        exact hb this
      · rw [List.getLast_cons h0]
        exact ih (n / 2) (by omega) h0

end Complexity.LogProg

namespace Complexity.LogProg

/-- `n + 1 ≤ 2^(⌊log₂ n⌋ + 1)`. -/
lemma succ_le_two_pow_log (n : ℕ) : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) n

/-- **Logarithms of polynomials are logarithmic**: `⌊log₂ (A (n+1)^c + B)⌋ + 1` is at most a
constant times `⌊log₂ n⌋ + 1`.

**Proof sketch.** With `L = ⌊log₂ n⌋`, `n + 1 ≤ 2^{L+1}`, `A < 2^A` and `B < 2^B`, so
`A (n+1)^c + B < 2^{A + B + c(L+1) + 1}`; take `K = A + B + c + 2`. -/
lemma log_poly_bound (A c B : ℕ) :
    ∃ K, ∀ n, Nat.log 2 (A * (n + 1) ^ c + B) + 1 ≤ K * (Nat.log 2 n + 1) := by
  refine ⟨A + B + c + 2, fun n => ?_⟩
  set L := Nat.log 2 n
  have h1 : (n + 1) ^ c ≤ 2 ^ (c * (L + 1)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left (succ_le_two_pow_log n) c
  have hA : A < 2 ^ A := Nat.lt_two_pow_self
  have hB : B < 2 ^ B := Nat.lt_two_pow_self
  have hy : A * (n + 1) ^ c + B < 2 ^ (A + B + c * (L + 1) + 1) := by
    have e1 : A * (n + 1) ^ c ≤ 2 ^ A * 2 ^ (c * (L + 1)) :=
      Nat.mul_le_mul hA.le h1
    have e2 : 2 ^ A * 2 ^ (c * (L + 1)) ≤ 2 ^ (A + B + c * (L + 1)) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have e3 : 2 ^ B ≤ 2 ^ (A + B + c * (L + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega
  have hlog : Nat.log 2 (A * (n + 1) ^ c + B) < A + B + c * (L + 1) + 1 := by
    rcases Nat.eq_zero_or_pos (A * (n + 1) ^ c + B) with h | h
    · rw [h]; simp
    · exact Nat.log_lt_of_lt_pow (by omega) hy
  have hle : A + B + 2 ≤ (A + B + 2) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have heq : (A + B + c + 2) * (L + 1) = (A + B + 2) * (L + 1) + c * (L + 1) := by ring
  rw [heq]
  generalize c * (L + 1) = P at hlog ⊢
  generalize (A + B + 2) * (L + 1) = Q at hle ⊢
  omega

end Complexity.LogProg
