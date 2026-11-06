/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan, Hydroxyi
-/
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Digits.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The binary length of a natural number

Machines and register programs store numbers as little-endian binary words `Nat.bits n` (least
significant bit first, no redundant zeros). This file is the one home of the elementary bounds on
the length `|Nat.bits n|` of such a word, below both the machine layer
(`TCSlib.Complexity.TuringMachine.Encoding` imports it) and the register-program layer
(`TCSlib.Complexity.SpaceComplexity.Machines.Bin` imports it). It imports no TCSlib module.

## Main definitions

None — this file states bounds on Mathlib's `Nat.bits` only.

## Main results

* `Turing.length_bits_le_self` — `|bits m| ≤ m`.
* `Complexity.LogProg.length_bits_le` — `|bits n| ≤ m` when `n < 2^m`;
  `Complexity.LogProg.length_bits_succ_le` — `|bits (m + 1)| ≤ e + 2` when `m ≤ 2^e + 1`.
* `Complexity.LogProg.lt_two_pow_bits` — `n < 2^{|bits n|}`.
* `Complexity.LogProg.two_pow_bits_le` — `2^{|bits L|} ≤ 2L` for `L ≥ 1`;
  `Complexity.LogProg.two_pow_bits_le_two_mul_add_one` — `2^{|bits n|} ≤ 2n + 1` for every `n`.
* `Complexity.LogProg.length_bits_mono` — `|bits n|` is monotone in `n`.
* `Complexity.LogProg.length_bits_le_log` — `|bits n| ≤ ⌊log₂ n⌋ + 1`;
  `Complexity.LogProg.length_bits_eq_log` — `|bits n| = ⌊log₂ n⌋ + 1` for `n ≠ 0`.
* `Complexity.LogProg.ofDigits_lt_two_pow` — a word's `Nat.ofDigits` value is below
  `2^{length}`. (The `bitsVal` form, `Complexity.LogProg.bitsVal_lt_two_pow`, stays with
  `bitsVal` in `Machines/Bin`.)

## Implementation notes

The file has two namespace roots, `Turing` and `Complexity.LogProg`, against the one-root rule of
`policy.md` §1: the declarations were moved here from `Encoding` and `Machines/Bin` (and
`lt_two_pow_bits` from `Randomized/SpaceAmplifyPoly`) with their full names kept, so that no
downstream reference is renamed (the NatBits dedup, decision D1; the user, 2026-11-06).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: counters in logarithmic space.)
-/

namespace Turing

/-- The binary expansion of `m` has at most `m` bits. -/
lemma length_bits_le_self (m : ℕ) : m.bits.length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

end Turing

namespace Complexity.LogProg

/-- The binary word of `n` has at most `m` letters when `n < 2^m`. -/
lemma length_bits_le {n m : ℕ} (h : n < 2 ^ m) : (Nat.bits n).length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

/-- A number `m ≤ 2 ^ e + 1` has at most `e + 2` binary digits after one increment: the width
bound for a register value `m` with `m ≤ 2 ^ e`.

**Proof sketch.** `m + 1 ≤ 2 ^ e + 2 < 4 · 2 ^ e = 2 ^ (e + 2)` since `2 ^ e ≥ 1`, then
`length_bits_le`. -/
lemma length_bits_succ_le {m e : ℕ} (h : m ≤ 2 ^ e + 1) : (Nat.bits (m + 1)).length ≤ e + 2 := by
  apply length_bits_le
  have : 2 ^ e + 2 < 2 ^ (e + 2) := by
    rw [pow_add]; have := Nat.one_le_two_pow (n := e); omega
  omega

/-- `n < 2^{|bits n|}`. -/
theorem lt_two_pow_bits (n : ℕ) : n < 2 ^ (Nat.bits n).length := by
  rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self n

/-- `2 ^ |bits L| ≤ 2L` for `L ≥ 1`.

**Proof sketch.** `|bits L| = Nat.size L ≥ 1`, and `2 ^ (Nat.size L - 1) ≤ L` (`Nat.size_le`), so
`2 ^ |bits L| = 2 · 2 ^ (Nat.size L - 1) ≤ 2L`. -/
lemma two_pow_bits_le (L : ℕ) (hL : 1 ≤ L) : 2 ^ (Nat.bits L).length ≤ 2 * L := by
  rw [Nat.size_eq_bits_len]
  have hpos : 1 ≤ Nat.size L := Nat.size_pos.mpr (by omega)
  have hlt : ¬ L < 2 ^ (Nat.size L - 1) := by
    rw [← Nat.size_le]; omega
  have e : 2 ^ Nat.size L = 2 * 2 ^ (Nat.size L - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- For every `n`, including `0`, two to the binary length of `n` is at most `2n + 1`:
`2 ^ |bits n| ≤ 2n + 1`. (Technical glue; the counter widths of [AB09, §4.1].)

**Proof sketch.** At `n = 0` the word is empty and `2 ^ 0 = 1`. Otherwise
`2 ^ |bits n| ≤ 2n` (`Complexity.LogProg.two_pow_bits_le`). -/
theorem two_pow_bits_le_two_mul_add_one (n : ℕ) : 2 ^ (Nat.bits n).length ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (two_pow_bits_le n hn).trans (Nat.le_succ _)

/-- Binary words of larger numbers are not shorter. -/
lemma length_bits_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size h

/-- The binary word of `n` has at most `⌊log₂ n⌋ + 1` letters. -/
lemma length_bits_le_log (n : ℕ) : (Nat.bits n).length ≤ Nat.log 2 n + 1 :=
  length_bits_le (Nat.lt_pow_succ_log_self (by norm_num) n)

/-- For `n ≠ 0`, the binary word of `n` has exactly `⌊log₂ n⌋ + 1` letters:
`|bits n| = Nat.log 2 n + 1`. (At `n = 0` the word is empty while the right side is `1`.)
(Technical glue; the logarithmic counter widths of [AB09, §4.1].)

**Proof sketch.** The upper bound is `Complexity.LogProg.length_bits_le_log`. For the lower
bound, `|bits n| = Nat.size n`, and `2 ^ ⌊log₂ n⌋ ≤ n` since `n ≠ 0`, so
`⌊log₂ n⌋ < Nat.size n`. -/
theorem length_bits_eq_log {n : ℕ} (hn : n ≠ 0) : (Nat.bits n).length = Nat.log 2 n + 1 := by
  refine le_antisymm (length_bits_le_log n) ?_
  rw [Nat.size_eq_bits_len]
  exact Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn))

/-- A word `w` of `|w|` letters, read as a little-endian binary number
`Nat.ofDigits 2 (w.map Bool.toNat)`, has value below `2 ^ |w|`. This is the `Nat.ofDigits` form
of `Complexity.LogProg.bitsVal_lt_two_pow`. (Technical glue; the binary counters of
[AB09, §4.1].)

**Proof sketch.** Every digit `b.toNat` is below `2`, so Mathlib's
`Nat.ofDigits_lt_base_pow_length` applies, and mapping keeps the length. -/
theorem ofDigits_lt_two_pow (w : List Bool) :
    Nat.ofDigits 2 (w.map Bool.toNat) < 2 ^ w.length := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 2) (l := w.map Bool.toNat) (by norm_num)
    (by
      intro d hd
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hd
      cases a <;> decide)
  rwa [List.length_map] at h

end Complexity.LogProg
