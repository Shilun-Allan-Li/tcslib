/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.ArithmeticDischarge
import TCSlib.Cryptography.NumberTheory.Euclid
import Mathlib.Data.Int.GCD

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The extended Euclidean algorithm as a polynomial-time machine

The field `ArithmeticFP.xgcd` of the hypothesis bundle asks for `xgcdStr ⟨a, b⟩ =
⟨⟦gcd(⟦a⟧, ⟦b⟧)⟧_{|b|}, ⟦(⟦a⟧ : Z_{⟦b⟧})⁻¹⟧_{|b|}⟩` to be polynomial-time, for **every** pair of
words: composite and degenerate moduli included (RSA's `d = e⁻¹ mod Φ(N)` is one). The inverse is
Mathlib's `ZMod.inv`: for `⟦b⟧ ≥ 1` it is the Bézout coefficient `Nat.gcdA (⟦a⟧ mod ⟦b⟧) ⟦b⟧`
reduced modulo `⟦b⟧`, and for `⟦b⟧ = 0` (`Z_0 = ℤ`) it is the sign of `⟦a⟧`. A Fermat inverse
`a^{b−2} mod b` would agree only at prime moduli, so this file runs the extended Euclidean
algorithm [PS10, Algorithm 43.2].

**The loop.** The state is `⟨b, ⟨⟨r', r⟩, ⟨s' mod b, s mod b⟩⟩⟩` (normalized little-endian
words), and one round follows Mathlib's `Nat.xgcdAux` recursion exactly
(`Nat.xgcdAux_rec`): with `q = ⌊r'/r⌋`,
`⟨r', r, s', s⟩ ↦ ⟨r, r' mod r, s, s' − q·s⟩`, keeping the Bézout coefficients only modulo `b`
(the recurrence is linear, so their residues follow it). States with `r = 0` are fixed. The
loop starts at `⟨b, a mod b, 0, 1⟩`, the arguments of `Nat.xgcd (a mod b) b`; when `r = 0` the
slot `s'` holds `Nat.gcdA (a mod b) b mod b` (`Nat.xgcd_zero_left`, `Nat.xgcdAux_val`).
The potential is the number of recursive calls of the textbook algorithm on `(r', r)`, plus one
(`NumberTheory.extEuclidCalls`), which a round lowers by one and which starts at most
`2|b| + 1` [PS10, Claim 43.3] (`NumberTheory.extEuclidCalls_le`); so `2(|z| + 1)` rounds of
`Complexity.BinArith.polyTimeComputable_iterate` suffice. The gcd is `BinArith.gcd`.

## Main definitions

* `TCSlib.Cryptography.Candidates.xgcdLoopStep`, `xgcdLoopInit`, `xgcdLoopOut` — the loop.
* `TCSlib.Cryptography.Candidates.xgcdInvWord` — the inverse as a little-endian word.

## Main results

* `TCSlib.Cryptography.Candidates.xgcdLoopOut_spec` — the loop computes the residue of
  `Nat.gcdA (a mod b) b`.
* `TCSlib.Cryptography.Candidates.xgcdInvWord_spec` — the word is `bits ((a : Z_b)⁻¹).val`.
* `TCSlib.Cryptography.Candidates.polyTimeComputable_xgcdStr_pairEncode` — the extended
  Euclidean algorithm is polynomial-time ([PS10, Algorithm 43.2, Claim 43.3]) on re-paired
  inputs, and `polyTimeComputable_xgcdStr` (the field `ArithmeticFP.xgcd`) on every word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 43.2, the extended Euclidean algorithm; Claim 43.3, its call bound.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§7.2, the binary-arithmetic machines.)
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory TCSlib.Cryptography.Encoding.BinaryArith

/-! ### The state and one round -/

/-- The new coefficient residue of a round on `⟨b, ⟨⟨r', r⟩, ⟨s', s⟩⟩⟩`:
`(s' + b − ((⌊r'/r⌋ · s) mod b)) mod b`, i.e. `(s' − ⌊r'/r⌋ s) mod b` on residues. -/
def xgcdCoefStep (S : List Bool) : List Bool :=
  BinArith.mod (pairEncode
    (BinArith.sub (pairEncode
      (BinArith.add (pairEncode (pairFstD (pairSndD (pairSndD S))) (pairFstD S)))
      (BinArith.mod (pairEncode
        (BinArith.mul (pairEncode
          (BinArith.div (pairEncode (pairFstD (pairFstD (pairSndD S)))
            (pairSndD (pairFstD (pairSndD S)))))
          (pairSndD (pairSndD (pairSndD S)))))
        (pairFstD S)))))
    (pairFstD S))

/-- The defining equation of `xgcdCoefStep`: on `S = ⟨b, ⟨⟨r', r⟩, ⟨s', s⟩⟩⟩` it is
`mod ⟨sub ⟨add ⟨s', b⟩, mod ⟨mul ⟨div ⟨r', r⟩, s⟩, b⟩⟩, b⟩` (slots read by the projections). -/
theorem xgcdCoefStep_eq (S : List Bool) :
    xgcdCoefStep S = BinArith.mod (pairEncode
      (BinArith.sub (pairEncode
        (BinArith.add (pairEncode (pairFstD (pairSndD (pairSndD S))) (pairFstD S)))
        (BinArith.mod (pairEncode
          (BinArith.mul (pairEncode
            (BinArith.div (pairEncode (pairFstD (pairFstD (pairSndD S)))
              (pairSndD (pairFstD (pairSndD S)))))
            (pairSndD (pairSndD (pairSndD S)))))
          (pairFstD S)))))
      (pairFstD S)) := rfl

/-- One round of the extended Euclidean loop on `S = ⟨b, ⟨⟨r', r⟩, ⟨s', s⟩⟩⟩`: if `r = 0` the
state is fixed; otherwise `⟨b, ⟨⟨r, r' mod r⟩, ⟨s, (s' − ⌊r'/r⌋ s) mod b⟩⟩⟩` [PS10,
Algorithm 43.2], in the form of Mathlib's `Nat.xgcdAux`. -/
def xgcdLoopStep (S : List Bool) : List Bool :=
  if decide (LogProg.bitsVal (pairSndD (pairFstD (pairSndD S))) = 0) then S
  else pairEncode (pairFstD S)
    (pairEncode
      (pairEncode (pairSndD (pairFstD (pairSndD S)))
        (BinArith.mod (pairEncode (pairFstD (pairFstD (pairSndD S)))
          (pairSndD (pairFstD (pairSndD S))))))
      (pairEncode (pairSndD (pairSndD (pairSndD S))) (xgcdCoefStep S)))

/-- The start of the loop on `z = ⟨a, b⟩`: `⟨b, ⟨⟨b, a mod b⟩, ⟨0, 1 mod b⟩⟩⟩`, the arguments of
`Nat.xgcd (a mod b) b`; for `⟦b⟧ = 0` the slot `r` is `0`, so the state is fixed. -/
def xgcdLoopInit (z : List Bool) : List Bool :=
  pairEncode (toLE (pairSndD z))
    (pairEncode
      (pairEncode (toLE (pairSndD z))
        (if decide (LogProg.bitsVal (toLE (pairSndD z)) = 0) then Nat.bits 0
          else BinArith.mod (pairEncode (toLE (pairFstD z)) (toLE (pairSndD z)))))
      (pairEncode (Nat.bits 0) (BinArith.mod (pairEncode (Nat.bits 1) (toLE (pairSndD z))))))

/-- The defining equation of `xgcdLoopStep`: a state whose slot `r` has value `0` is kept,
otherwise `⟨b, ⟨⟨r, mod ⟨r', r⟩⟩, ⟨s, xgcdCoefStep S⟩⟩⟩`. -/
theorem xgcdLoopStep_eq (S : List Bool) :
    xgcdLoopStep S =
      if decide (LogProg.bitsVal (pairSndD (pairFstD (pairSndD S))) = 0) then S
      else pairEncode (pairFstD S)
        (pairEncode
          (pairEncode (pairSndD (pairFstD (pairSndD S)))
            (BinArith.mod (pairEncode (pairFstD (pairFstD (pairSndD S)))
              (pairSndD (pairFstD (pairSndD S))))))
          (pairEncode (pairSndD (pairSndD (pairSndD S))) (xgcdCoefStep S))) := rfl

/-- The defining equation of `xgcdLoopInit`:
`xgcdLoopInit z = ⟨toLE b, ⟨⟨toLE b, r₀⟩, ⟨bits 0, mod ⟨bits 1, toLE b⟩⟩⟩⟩` with
`r₀ = bits 0` if `bitsVal (toLE b) = 0` and `r₀ = mod ⟨toLE a, toLE b⟩` otherwise. -/
theorem xgcdLoopInit_eq (z : List Bool) :
    xgcdLoopInit z =
      pairEncode (toLE (pairSndD z))
        (pairEncode
          (pairEncode (toLE (pairSndD z))
            (if decide (LogProg.bitsVal (toLE (pairSndD z)) = 0) then Nat.bits 0
              else BinArith.mod (pairEncode (toLE (pairFstD z)) (toLE (pairSndD z)))))
          (pairEncode (Nat.bits 0)
            (BinArith.mod (pairEncode (Nat.bits 1) (toLE (pairSndD z)))))) := rfl

/-- The output of the loop on `z`: the slot `s'` after `2(|z| + 1)` rounds. -/
def xgcdLoopOut (z : List Bool) : List Bool :=
  pairFstD (pairSndD (pairSndD (xgcdLoopStep^[2 * (z.length + 1) ^ 1] (xgcdLoopInit z))))

/-- The defining equation of `xgcdLoopOut`: the slot `s'` of
`xgcdLoopStep^[2(|z|+1)] (xgcdLoopInit z)`. -/
theorem xgcdLoopOut_eq (z : List Bool) :
    xgcdLoopOut z =
      pairFstD (pairSndD (pairSndD (xgcdLoopStep^[2 * (z.length + 1) ^ 1] (xgcdLoopInit z)))) :=
  rfl

/-- The encoded loop state of numbers `b, r', r, s', s` (all words normalized). -/
def xgcdState (b r' r s' s : ℕ) : List Bool :=
  pairEncode (Nat.bits b)
    (pairEncode (pairEncode (Nat.bits r') (Nat.bits r)) (pairEncode (Nat.bits s') (Nat.bits s)))

/-- The defining equation of `xgcdState`:
`xgcdState b r' r s' s = ⟨bits b, ⟨⟨bits r', bits r⟩, ⟨bits s', bits s⟩⟩⟩`. -/
theorem xgcdState_eq (b r' r s' s : ℕ) :
    xgcdState b r' r s' s =
      pairEncode (Nat.bits b)
        (pairEncode (pairEncode (Nat.bits r') (Nat.bits r))
          (pairEncode (Nat.bits s') (Nat.bits s))) := rfl

/-- Glue. The residue arithmetic of a round: for `b > 0`, natural residues `S' = s' mod b`,
`S = s mod b` and any `q`, `(S' + b − (q S mod b)) mod b = (s' − q s) mod b` (as a natural
number). -/
theorem xgcd_coef_residue {b : ℕ} (hb : 0 < b) (q : ℕ) (s' s : ℤ) :
    ((s' % b).toNat + b - q * (s % b).toNat % b) % b = ((s' - q * s) % b).toNat := by
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have h1 : (((s' % b).toNat : ℕ) : ℤ) = s' % b := Int.toNat_of_nonneg (Int.emod_nonneg _ hb'.ne')
  have h2 : (((s % b).toNat : ℕ) : ℤ) = s % b := Int.toNat_of_nonneg (Int.emod_nonneg _ hb'.ne')
  have hlt : q * (s % b).toNat % b ≤ (s' % b).toNat + b :=
    (Nat.mod_lt _ hb).le.trans (Nat.le_add_left _ _)
  apply Int.natCast_inj.mp
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hb'.ne'), Int.natCast_mod, Nat.cast_sub hlt,
    Nat.cast_add, Int.natCast_mod, Nat.cast_mul, h1, h2]
  have hm : ((s' % b + b - q * (s % b) % b) : ℤ) ≡ s' - q * s [ZMOD b] := by
    have e1 : (s' % b : ℤ) ≡ s' [ZMOD b] := Int.mod_modEq s' b
    have e2 : (q * (s % b) % b : ℤ) ≡ q * s [ZMOD b] :=
      (Int.mod_modEq _ b).trans ((Int.mod_modEq s b).mul_left _)
    have e3 : (b : ℤ) ≡ 0 [ZMOD b] := Int.modEq_zero_iff_dvd.mpr dvd_rfl
    have := (e1.add e3).sub e2
    rwa [add_zero] at this
  exact hm.eq

/-- **One round of the loop** on a state of numbers with `r ≠ 0`, `b > 0`:
`xgcdLoopStep ⟨b, r', r, s' mod b, s mod b⟩ = ⟨b, r, r' mod r, s mod b, (s' − ⌊r'/r⌋ s) mod b⟩`.

**Proof sketch.** The slot `r` reads `bits r` with value `r ≠ 0`, so the round is taken; each
machine (`div`, `mul`, `mod`, `add`, `sub`) is read through its `_pairEncode` equation on
normalized words, and `xgcd_coef_residue` identifies the coefficient. -/
theorem xgcdLoopStep_state {b r' r : ℕ} (hb : 0 < b) (hr : r ≠ 0) (s' s : ℤ) :
    xgcdLoopStep (xgcdState b r' r ((s' % b).toNat) ((s % b).toNat)) =
      xgcdState b r (r' % r) ((s % b).toNat) (((s' - (r' / r : ℕ) * s) % b).toNat) := by
  rw [xgcdLoopStep_eq, xgcdCoefStep_eq, xgcdState_eq, xgcdState_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, LogProg.bitsVal_bits,
    BinArith.div_pairEncode,
    BinArith.mul_pairEncode, BinArith.mod_pairEncode, BinArith.add_pairEncode,
    BinArith.sub_pairEncode, hr, decide_false, Bool.false_eq_true, if_false]
  rw [xgcd_coef_residue hb]

/-- A state with `r = 0` is fixed by the round. -/
theorem xgcdLoopStep_of_zero (S : List Bool)
    (h : LogProg.bitsVal (pairSndD (pairFstD (pairSndD S))) = 0) : xgcdLoopStep S = S := by
  rw [xgcdLoopStep_eq, if_pos (decide_eq_true h)]

/-! ### Invariant and potential -/

/-- The invariant of the loop on `z = ⟨a, b⟩` with `b > 0`: the state is
`⟨b, r', r, s' mod b, s mod b⟩` with `r, r' ≤ b` for some integers `s, t, s', t'` such that
Mathlib's recursion from `(r, s, t, r', s', t')` ends where it ends from the start
`(a mod b, 1, 0, b, 0, 1)`. -/
def XgcdLoopInv (a b : ℕ) (S : List Bool) : Prop :=
  ∃ (r r' : ℕ) (s t s' t' : ℤ), r ≤ b ∧ r' ≤ b ∧
    S = xgcdState b r' r ((s' % b).toNat) ((s % b).toNat) ∧
    Nat.xgcdAux r s t r' s' t' = Nat.xgcdAux (a % b) 1 0 b 0 1

/-- The reader of `XgcdLoopInv`: `XgcdLoopInv a b S` holds iff `S` is an encoded state
`⟨b, r', r, s' mod b, s mod b⟩` with `r, r' ≤ b` and
`xgcdAux r s t r' s' t' = xgcdAux (a mod b) 1 0 b 0 1` for some `s, t, s', t'`. -/
theorem xgcdLoopInv_iff (a b : ℕ) (S : List Bool) :
    XgcdLoopInv a b S ↔ ∃ (r r' : ℕ) (s t s' t' : ℤ), r ≤ b ∧ r' ≤ b ∧
      S = xgcdState b r' r ((s' % b).toNat) ((s % b).toNat) ∧
      Nat.xgcdAux r s t r' s' t' = Nat.xgcdAux (a % b) 1 0 b 0 1 := Iff.rfl

/-- The potential of a state: `0` when `r = 0`, else the number of recursive calls of the
textbook algorithm on `(r', r)` plus one ([PS10, Claim 43.3], `extEuclidCalls`). -/
def xgcdLoopMeasure (S : List Bool) : ℕ :=
  if LogProg.bitsVal (pairSndD (pairFstD (pairSndD S))) = 0 then 0
  else extEuclidCalls (LogProg.bitsVal (pairFstD (pairFstD (pairSndD S))))
    (LogProg.bitsVal (pairSndD (pairFstD (pairSndD S)))) + 1

/-- The potential of an encoded state of numbers: `0` if `r = 0`, else `calls(r', r) + 1`. -/
theorem xgcdLoopMeasure_state (b r' r s' s : ℕ) :
    xgcdLoopMeasure (xgcdState b r' r s' s) = if r = 0 then 0 else extEuclidCalls r' r + 1 := by
  rw [xgcdLoopMeasure, xgcdState_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, LogProg.bitsVal_bits]

/-- **The round keeps the invariant, lowers a positive potential and fixes potential `0`.**

**Proof sketch.** With `r = 0` the state is fixed. Otherwise `xgcdLoopStep_state` gives the new
state `⟨b, r, r' mod r, s mod b, (s' − q s) mod b⟩`, which is the state of Mathlib's next
call (`Nat.xgcdAux_rec`), so the invariant holds with `(r' mod r, s' − q s, t' − q t, r, s, t)`.
If `r' mod r = 0` the potential drops to `0`; otherwise the textbook count satisfies
`calls(r', r) = calls(r, r' mod r) + 1` (`extEuclidCalls_of_mod_ne_zero`). -/
theorem xgcdLoopInv_step {a b : ℕ} (hb : 0 < b) {S : List Bool} (h : XgcdLoopInv a b S) :
    XgcdLoopInv a b (xgcdLoopStep S) ∧
      (0 < xgcdLoopMeasure S → xgcdLoopMeasure (xgcdLoopStep S) < xgcdLoopMeasure S) ∧
      (xgcdLoopMeasure S = 0 → xgcdLoopStep S = S) := by
  obtain ⟨r, r', s, t, s', t', hrb, hr'b, rfl, hx⟩ := h
  by_cases hr : r = 0
  · have hfix : xgcdLoopStep (xgcdState b r' r ((s' % b).toNat) ((s % b).toNat)) =
        xgcdState b r' r ((s' % b).toNat) ((s % b).toNat) := by
      apply xgcdLoopStep_of_zero
      rw [xgcdState_eq]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, LogProg.bitsVal_bits, hr]
    rw [hfix, xgcdLoopMeasure_state, if_pos hr]
    exact ⟨⟨r, r', s, t, s', t', hrb, hr'b, rfl, hx⟩, fun h => absurd h (lt_irrefl 0),
      fun _ => rfl⟩
  have hrpos := Nat.pos_of_ne_zero hr
  rw [xgcdLoopStep_state hb hr]
  refine ⟨⟨r' % r, r, s' - (r' / r : ℕ) * s, t' - (r' / r : ℕ) * t, s, t,
    (Nat.mod_lt _ hrpos).le.trans hrb, hrb, rfl, ?_⟩, ?_, ?_⟩
  · rw [← hx, Nat.xgcdAux_rec hrpos]
    push_cast
    rfl
  · intro _
    rw [xgcdLoopMeasure_state, xgcdLoopMeasure_state, if_neg hr]
    split_ifs with h0
    · omega
    · rw [extEuclidCalls_of_mod_ne_zero hr h0]
      omega
  · intro h0
    rw [xgcdLoopMeasure_state, if_neg hr] at h0
    omega

/-! ### The loop's start and output -/

/-- The start of the loop for `b > 0` is the encoded state `⟨b, b, a mod b, 0 mod b, 1 mod b⟩`
of Mathlib's start `(a mod b, 1, 0, b, 0, 1)`, and it satisfies the invariant. -/
theorem xgcdLoopInv_init (z : List Bool) (hb : 0 < listToNat (pairSndD z)) :
    XgcdLoopInv (listToNat (pairFstD z)) (listToNat (pairSndD z)) (xgcdLoopInit z) := by
  set a := listToNat (pairFstD z)
  set b := listToNat (pairSndD z)
  refine ⟨a % b, b, 1, 0, 0, 1, (Nat.mod_lt _ hb).le, le_rfl, ?_, rfl⟩
  have hb0 : LogProg.bitsVal (toLE (pairSndD z)) ≠ 0 := by
    rw [bitsVal_toLE]; exact hb.ne'
  have h1 : ((1 : ℤ) % (b : ℤ)).toNat = 1 % b := by
    rw [← Int.natCast_one, ← Int.natCast_mod, Int.toNat_natCast]
  rw [xgcdLoopInit_eq, if_neg (by simpa using hb0), xgcdState_eq, toLE_eq_natBits, toLE_eq_natBits,
    BinArith.mod_pairEncode, BinArith.mod_pairEncode, Int.zero_emod, Int.toNat_zero, h1]

/-- Glue. Every encoded state of numbers at most `b` has length at most `11 (|bits b| + 1)`. -/
theorem length_xgcdState_le {b r' r s' s : ℕ} (h1 : r' ≤ b) (h2 : r ≤ b) (h3 : s' ≤ b)
    (h4 : s ≤ b) : (xgcdState b r' r s' s).length ≤ 11 * ((Nat.bits b).length + 1) := by
  have hl : ∀ {n : ℕ}, n ≤ b → (Nat.bits n).length ≤ (Nat.bits b).length := fun hn => by
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]; exact Nat.size_le_size hn
  have := hl h1; have := hl h2; have := hl h3; have := hl h4
  rw [xgcdState_eq]
  simp only [length_pairEncode]
  omega

/-- **The loop computes the Bézout residue**: for `b = ⟦pairSndD z⟧ > 0` and
`a = ⟦pairFstD z⟧`, `xgcdLoopOut z = bits ((gcdA (a mod b) b) mod b)`.

**Proof sketch.** The invariant holds along the orbit (`iterate_invariant`). The potential
starts at most `2|b| + 1 ≤ 2(|z| + 1)`: it is `0` if `a mod b = 0` and otherwise
`calls(b, a mod b) + 1` with `a mod b < b < 2^{|b|}` (`extEuclidCalls_le`), so after
`2(|z| + 1)` rounds it is `0` (`iterate_measure_eq_zero`) and `r = 0`. Then Mathlib's
recursion stops (`Nat.xgcd_zero_left`), so `s' = gcdA (a mod b) b` (`Nat.xgcdAux_val`,
`Nat.xgcd_val`), and the slot `s'` holds its residue. -/
theorem xgcdLoopOut_spec (z : List Bool) (hb : 0 < listToNat (pairSndD z)) :
    xgcdLoopOut z = Nat.bits ((Nat.gcdA (listToNat (pairFstD z) % listToNat (pairSndD z))
      (listToNat (pairSndD z)) % (listToNat (pairSndD z) : ℤ)).toNat) := by
  set a := listToNat (pairFstD z)
  set b := listToNat (pairSndD z)
  have hI := fun S (h : XgcdLoopInv a b S) => (xgcdLoopInv_step hb h).1
  have hμ := BinArith.iterate_measure_eq_zero (g := xgcdLoopStep) (XgcdLoopInv a b)
    xgcdLoopMeasure hI
    (fun _ h => (xgcdLoopInv_step hb h).2.1) (fun _ h => (xgcdLoopInv_step hb h).2.2)
    (2 * (z.length + 1) ^ 1) _ (xgcdLoopInv_init z hb) (by
      rw [xgcdLoopInit_eq, if_neg (by rw [bitsVal_toLE]; simpa using hb.ne'), toLE_eq_natBits,
        toLE_eq_natBits, BinArith.mod_pairEncode, BinArith.mod_pairEncode, ← xgcdState_eq,
        xgcdLoopMeasure_state]
      split_ifs with h0
      · exact Nat.zero_le _
      · have hlt : b < 2 ^ (pairSndD z).length := listToNat_lt_two_pow _
        have hc : extEuclidCalls b (a % b) ≤ 2 * (pairSndD z).length :=
          extEuclidCalls_le (pairSndD z).length b (a % b) (Nat.mod_lt _ hb) hlt
        have := length_pairSndD_le z
        change extEuclidCalls b (a % b) + 1 ≤ 2 * (z.length + 1) ^ 1
        rw [pow_one]
        omega)
  obtain ⟨r, r', s, t, s', t', -, -, he, hx⟩ :=
    BinArith.iterate_invariant (XgcdLoopInv a b) hI (2 * (z.length + 1) ^ 1)
      (xgcdLoopInv_init z hb)
  rw [he, xgcdLoopMeasure_state] at hμ
  have hr : r = 0 := by
    by_contra hr; rw [if_neg hr] at hμ; omega
  subst hr
  rw [Nat.xgcd_zero_left, Nat.xgcdAux_val, Nat.xgcd_val] at hx
  rw [xgcdLoopOut_eq, he, xgcdState_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hs : s' = Nat.gcdA (a % b) b := (Prod.mk.inj (Prod.mk.inj hx).2).1
  rw [hs]

/-- Glue. Every state of the loop has length at most `11 (|z| + 1)`, on every input `z`.

**Proof sketch.** For `⟦b⟧ = 0` the start has `r = 0` and is fixed (`Function.iterate_fixed`),
and its words are short. For `⟦b⟧ > 0` the invariant bounds every slot by `b`
(`length_xgcdState_le`), and `|bits b| = |toLE b| ≤ |b| ≤ |z|`. -/
theorem length_xgcdLoop_le (z : List Bool) (i : ℕ) :
    (xgcdLoopStep^[i] (xgcdLoopInit z)).length ≤ 11 * (z.length + 1) ^ 1 := by
  have hbz : (toLE (pairSndD z)).length ≤ z.length :=
    (length_toLE_le _).trans (length_pairSndD_le z)
  rw [pow_one]
  by_cases hb : listToNat (pairSndD z) = 0
  · have h0 : LogProg.bitsVal (toLE (pairSndD z)) = 0 := by rw [bitsVal_toLE, hb]
    have hinit : xgcdLoopInit z = pairEncode (toLE (pairSndD z))
        (pairEncode (pairEncode (toLE (pairSndD z)) (Nat.bits 0))
          (pairEncode (Nat.bits 0) (Nat.bits 1))) := by
      rw [xgcdLoopInit_eq, if_pos (decide_eq_true h0), toLE_eq_natBits, BinArith.mod_pairEncode, hb,
        Nat.mod_zero]
    have hfix : xgcdLoopStep (xgcdLoopInit z) = xgcdLoopInit z := by
      apply xgcdLoopStep_of_zero
      rw [hinit]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, LogProg.bitsVal_bits]
    rw [Function.iterate_fixed hfix, hinit]
    have hb1 : (Nat.bits 1).length = 1 := by rw [Nat.size_eq_bits_len, Nat.size_one]
    simp only [length_pairEncode, Nat.zero_bits, List.length_nil, hb1]
    omega
  · obtain ⟨r, r', s, t, s', t', hrb, hr'b, he, -⟩ := BinArith.iterate_invariant
      (XgcdLoopInv (listToNat (pairFstD z)) (listToNat (pairSndD z)))
      (fun S h => (xgcdLoopInv_step (Nat.pos_of_ne_zero hb) h).1) i
      (xgcdLoopInv_init z (Nat.pos_of_ne_zero hb))
    have hm : ∀ x : ℤ, (x % (listToNat (pairSndD z) : ℤ)).toNat ≤ listToNat (pairSndD z) :=
      fun x => by
        have h1 := Int.emod_lt_of_pos x (by exact_mod_cast Nat.pos_of_ne_zero hb :
          (0 : ℤ) < listToNat (pairSndD z))
        omega
    rw [he]
    have := length_xgcdState_le hr'b hrb (hm s') (hm s)
    rw [← toLE_eq_natBits] at this
    omega

/-- Glue. One round of the loop is polynomial-time: a zero test on `r`, then the `div`, `mul`,
`mod`, `add`, `sub` machines of `Complexity.BinArith` on the slots. -/
theorem polyTimeComputable_xgcdLoopStep : PolyTimeComputable xgcdLoopStep := by
  have hB : PolyTimeComputable fun S => pairFstD S := polyTimeComputable_pairFstD
  have hR' : PolyTimeComputable fun S => pairFstD (pairFstD (pairSndD S)) :=
    polyTimeComputable_pairFstD.comp' BinArith.polyTimeComputable_slot2
  have hR : PolyTimeComputable fun S => pairSndD (pairFstD (pairSndD S)) :=
    polyTimeComputable_pairSndD.comp' BinArith.polyTimeComputable_slot2
  have hS' : PolyTimeComputable fun S => pairFstD (pairSndD (pairSndD S)) :=
    polyTimeComputable_pairFstD.comp' BinArith.polyTimeComputable_slot3
  have hS : PolyTimeComputable fun S => pairSndD (pairSndD (pairSndD S)) :=
    polyTimeComputable_pairSndD.comp' BinArith.polyTimeComputable_slot3
  have hc : PolyTimeComputable xgcdCoefStep :=
    BinArith.polyTimeComputable_mod.comp' ((BinArith.polyTimeComputable_sub.comp'
      ((BinArith.polyTimeComputable_add.comp' (hS'.pairEncode hB)).pairEncode
        (BinArith.polyTimeComputable_mod.comp' ((BinArith.polyTimeComputable_mul.comp'
          ((BinArith.polyTimeComputable_div.comp' (hR'.pairEncode hR)).pairEncode hS)).pairEncode
            hB)))).pairEncode hB)
  exact polyTimeComputable_ite (BinArith.polyTimeComputable_isZero.comp' hR) polyTimeComputable_id
    (hB.pairEncode ((hR.pairEncode (BinArith.polyTimeComputable_mod.comp'
      (hR'.pairEncode hR))).pairEncode (hS.pairEncode hc)))

/-- Glue. The start of the loop is polynomial-time. -/
theorem polyTimeComputable_xgcdLoopInit : PolyTimeComputable xgcdLoopInit := by
  have hb : PolyTimeComputable fun z => toLE (pairSndD z) := polyTimeComputable_toLE_pairSndD
  exact hb.pairEncode ((hb.pairEncode (polyTimeComputable_ite
    (BinArith.polyTimeComputable_isZero.comp' hb) (polyTimeComputable_const _)
    (BinArith.polyTimeComputable_mod.comp' polyTimeComputable_toLE_pair))).pairEncode
    ((polyTimeComputable_const _).pairEncode
      (BinArith.polyTimeComputable_mod.comp' ((polyTimeComputable_const _).pairEncode hb))))

/-- **The extended Euclidean loop is polynomial-time** [PS10, Claim 43.3]: `2(|z| + 1)` rounds
of a polynomial-time round on states of length at most `11(|z| + 1)`
(`BinArith.polyTimeComputable_iterate`, `length_xgcdLoop_le`). -/
theorem polyTimeComputable_xgcdLoopOut : PolyTimeComputable xgcdLoopOut :=
  (BinArith.polyTimeComputable_slot2.comp' (polyTimeComputable_pairSndD.comp'
    (BinArith.polyTimeComputable_iterate polyTimeComputable_xgcdLoopStep
      polyTimeComputable_xgcdLoopInit 2 1 11 1 fun z i _ => length_xgcdLoop_le z i))).congr
    fun z => (xgcdLoopOut_eq z).symm

/-! ### The inverse and the field -/

/-- The inverse of `⟦a⟧` modulo `⟦b⟧` as a little-endian word, for `z = ⟨a, b⟩`: for `⟦b⟧ = 0`
the sign of `⟦a⟧` (`bits 0` or `bits 1`), otherwise the loop's output. -/
def xgcdInvWord (z : List Bool) : List Bool :=
  if decide (LogProg.bitsVal (toLE (pairSndD z)) = 0) then
    (if decide (LogProg.bitsVal (toLE (pairFstD z)) = 0) then Nat.bits 0 else Nat.bits 1)
  else xgcdLoopOut z

/-- **The inverse word is Mathlib's `ZMod.inv`**: `xgcdInvWord z = bits ((⟦a⟧ : Z_{⟦b⟧})⁻¹).val`
for `a = pairFstD z`, `b = pairSndD z`, on every word.

**Proof sketch.** For `⟦b⟧ = 0`, `Z_0 = ℤ`, the inverse is the sign and its value is
`[⟦a⟧ ≠ 0]` (`Int.natAbs_sign`). For `⟦b⟧ = n + 1`, Mathlib's inverse is
`gcdA ((⟦a⟧ : Z_b).val) b` cast to `Z_b` (by definition), `(⟦a⟧ : Z_b).val = ⟦a⟧ mod b`
(`ZMod.val_natCast`) and the value of an integer cast is its residue (`ZMod.val_intCast`); that
is `xgcdLoopOut_spec`. -/
theorem xgcdInvWord_spec (z : List Bool) :
    xgcdInvWord z = Nat.bits
      ((listToNat (pairFstD z) : ZMod (listToNat (pairSndD z)))⁻¹).val := by
  rw [xgcdInvWord, bitsVal_toLE, bitsVal_toLE]
  rcases hb : listToNat (pairSndD z) with _ | n
  · rw [if_pos (decide_eq_true rfl)]
    have hv : ((listToNat (pairFstD z) : ZMod 0)⁻¹).val =
        if (listToNat (pairFstD z) : ℤ) = 0 then 0 else 1 := Int.natAbs_sign _
    rw [hv]
    by_cases ha : listToNat (pairFstD z) = 0
    · rw [if_pos (decide_eq_true ha), if_pos (by exact_mod_cast ha)]
    · rw [if_neg (by simpa using ha), if_neg (by exact_mod_cast ha)]
  · rw [if_neg (by simp), xgcdLoopOut_spec z (by omega), hb]
    have hinv : ((listToNat (pairFstD z) : ZMod (n + 1)))⁻¹ =
        ((Nat.gcdA ((listToNat (pairFstD z) : ZMod (n + 1)).val) (n + 1) : ℤ) : ZMod (n + 1)) :=
      rfl
    have hv := ZMod.val_intCast (n := n + 1)
      (Nat.gcdA ((listToNat (pairFstD z) : ZMod (n + 1)).val) (n + 1))
    rw [hinv, ZMod.val_natCast]
    rw [ZMod.val_natCast] at hv
    rw [← hv, Int.toNat_natCast]

/-- Glue. The inverse word is polynomial-time (two zero tests, constants and the loop). -/
theorem polyTimeComputable_xgcdInvWord : PolyTimeComputable xgcdInvWord :=
  polyTimeComputable_ite (BinArith.polyTimeComputable_isZero.comp' polyTimeComputable_toLE_pairSndD)
    (polyTimeComputable_ite
      (BinArith.polyTimeComputable_isZero.comp' polyTimeComputable_toLE_pairFstD)
      (polyTimeComputable_const _) (polyTimeComputable_const _))
    polyTimeComputable_xgcdLoopOut

/-- **The extended Euclidean algorithm is polynomial-time** [PS10, Algorithm 43.2, Claim 43.3]
on re-paired inputs: `z ↦ xgcdStr ⟨a, b⟩ = ⟨⟦gcd(⟦a⟧, ⟦b⟧)⟧_{|b|}, ⟦(⟦a⟧ : Z_{⟦b⟧})⁻¹⟧_{|b|}⟩`
with `a = pairFstD z`, `b = pairSndD z`, for every modulus (composite, `⟦b⟧ = 1` and
`⟦b⟧ = 0` included).

**Deviation:** [PS10] computes the inverse of a unit; the bundle's value is Mathlib's
`ZMod.inv` on every residue, which the loop computes as the Bézout coefficient of
`Nat.xgcd (a mod b) b` modulo `b`.

**Proof sketch.** The gcd is `BinArith.gcd` on `⟨toLE a, toLE b⟩` (`BinArith.gcd_pairEncode`),
the inverse is `xgcdInvWord` (`xgcdInvWord_spec`), and both are written at width `|b|` with
`fromLEPoly` at the template `b` (`fromLEPoly_var_bits`); `xgcdStr_pairEncode` reads the
bundle's value. -/
theorem polyTimeComputable_xgcdStr_pairEncode :
    PolyTimeComputable fun z => xgcdStr (pairEncode (pairFstD z) (pairSndD z)) :=
  ((polyTimeComputable_fromLEPoly_var polyTimeComputable_pairSndD
      (BinArith.polyTimeComputable_gcd.comp' polyTimeComputable_toLE_pair)).pairEncode
    (polyTimeComputable_fromLEPoly_var polyTimeComputable_pairSndD
      polyTimeComputable_xgcdInvWord)).congr fun z => by
    rw [toLE_pair_eq, BinArith.gcd_pairEncode, xgcdInvWord_spec, fromLEPoly_var_bits,
      fromLEPoly_var_bits, xgcdStr_pairEncode]

/-- **The extended Euclidean algorithm is polynomial-time** (the field `ArithmeticFP.xgcd`)
[PS10, Algorithm 43.2, Claim 43.3]: `PolyTimeComputable xgcdStr`, from
`polyTimeComputable_xgcdStr_pairEncode` and `xgcdStr_eq`. -/
theorem polyTimeComputable_xgcdStr : PolyTimeComputable xgcdStr :=
  polyTimeComputable_xgcdStr_pairEncode.congr fun z => by rw [xgcdStr_pairEncode, xgcdStr_eq]

end TCSlib.Cryptography.Candidates
