/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Div
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.ModEq

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Modular exponentiation and the gcd in polynomial time

Modular exponentiation `a^n mod p` by repeated squaring is [AB09, Exercise 7.3]; the gcd by
Euclid's algorithm is infrastructure for [AB09 §7.2] (the primality test of §7.2.2 checks
`gcd(N, A) > 1`), not itself a result of the book. Both are loops of
`Complexity.BinArith.polyTimeComputable_iterate`. A triple is `⟨a, ⟨n, p⟩⟩`.

## Main definitions

* `Complexity.BinArith.powMod` — `a^n mod p` on `⟨a, ⟨n, p⟩⟩` (`0` when `p = 0`).
* `Complexity.BinArith.gcd` — the gcd of the two components of a pair.

## Main results

* `Complexity.BinArith.polyTimeComputable_powMod` — [AB09, Exercise 7.3].
* `Complexity.BinArith.polyTimeComputable_gcd`.

## Divergences

* For `p = 0` the book's question is void; `powMod` then returns `0` rather than Lean's
  `a^n % 0 = a^n`, whose binary length is exponential in the input length.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.2; Exercise 7.3.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### Modular exponentiation -/

/-- `a^n mod p` on `z = ⟨a, ⟨n, p⟩⟩` (by value), as a binary word; `0` when `p = 0`. -/
def powMod (z : List Bool) : List Bool :=
  Nat.bits (if bitsVal (pairSndD (pairSndD z)) = 0 then 0
    else bitsVal (pairFstD z) ^ bitsVal (pairFstD (pairSndD z)) % bitsVal (pairSndD (pairSndD z)))

/-- `powMod` on encoded numbers with `p ≠ 0` is `a^n % p`. -/
theorem powMod_pairEncode (a n p : ℕ) (hp : p ≠ 0) :
    powMod (pairEncode (Nat.bits a) (pairEncode (Nat.bits n) (Nat.bits p))) =
      Nat.bits (a ^ n % p) := by
  simp [powMod, bitsVal_bits, hp]

/-- One round of repeated squaring on `⟨p, ⟨E, ⟨b, acc⟩⟩⟩`: if the low bit of `E` is set,
`acc := acc·b mod p`; then `b := b² mod p` and `E` loses its low bit. States with `E = []`
or `p = 0` are fixed. -/
def powStep (S : List Bool) : List Bool :=
  if isNilB (pairFstD (pairSndD S)) || decide (bitsVal (pairFstD S) = 0) then S
  else pairEncode (pairFstD S) (pairEncode ((pairFstD (pairSndD S)).drop 1)
    (pairEncode (mod (pairEncode (mul (pairEncode (pairFstD (pairSndD (pairSndD S)))
        (pairFstD (pairSndD (pairSndD S))))) (pairFstD S)))
      (if (pairFstD (pairSndD S)).headD false then
        mod (pairEncode (mul (pairEncode (pairSndD (pairSndD (pairSndD S)))
          (pairFstD (pairSndD (pairSndD S))))) (pairFstD S))
      else pairSndD (pairSndD (pairSndD S)))))

/-- A repeated-squaring round is polynomial-time. -/
theorem polyTimeComputable_powStep : PolyTimeComputable powStep := by
  have hs3 : PolyTimeComputable (fun S => pairFstD (pairSndD (pairSndD S))) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_slot3
  have hmm : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
      PolyTimeComputable (fun S => mod (pairEncode (mul (pairEncode (f S) (g S))) (pairFstD S))) :=
    fun hf hg => polyTimeComputable_mod.comp
      ((polyTimeComputable_mul.comp (hf.pairEncode hg)).pairEncode polyTimeComputable_pairFstD)
  unfold powStep
  refine polyTimeComputable_ite (polyTimeComputable_or
    (polyTimeComputable_isNil.comp polyTimeComputable_slot2)
    (polyTimeComputable_isZero.comp polyTimeComputable_pairFstD)) polyTimeComputable_id ?_
  exact polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp polyTimeComputable_slot2).pairEncode
      ((hmm hs3 hs3).pairEncode (polyTimeComputable_ite
        (polyTimeComputable_headD.comp polyTimeComputable_slot2) (hmm polyTimeComputable_slot4 hs3)
        polyTimeComputable_slot4)))

/-- The input state `⟨p, ⟨n, ⟨a mod p, 1 mod p⟩⟩⟩` of the repeated-squaring loop. -/
def powInit (z : List Bool) : List Bool :=
  pairEncode (pairSndD (pairSndD z)) (pairEncode (pairFstD (pairSndD z))
    (pairEncode (mod (pairEncode (pairFstD z) (pairSndD (pairSndD z))))
      (mod (pairEncode [true] (pairSndD (pairSndD z))))))

/-- The invariant of the repeated-squaring loop on `z = ⟨a, ⟨n, p⟩⟩`: `b` and `acc` are
normalized and short, `E` is no longer than `n`, and for `p ≠ 0` they are reduced and
`acc · b^E ≡ a^n (mod p)`. -/
def PowInv (z S : List Bool) : Prop :=
  ∃ E b acc, S = pairEncode (pairSndD (pairSndD z)) (pairEncode E (pairEncode b acc)) ∧
    E.length ≤ (pairFstD (pairSndD z)).length ∧ b = Nat.bits (bitsVal b) ∧
    acc = Nat.bits (bitsVal acc) ∧
    b.length ≤ (pairFstD z).length + (pairSndD (pairSndD z)).length ∧
    acc.length ≤ 1 + (pairSndD (pairSndD z)).length ∧
    (0 < bitsVal (pairSndD (pairSndD z)) →
      bitsVal b < bitsVal (pairSndD (pairSndD z)) ∧ bitsVal acc < bitsVal (pairSndD (pairSndD z)) ∧
      Nat.ModEq (bitsVal (pairSndD (pairSndD z))) (bitsVal acc * bitsVal b ^ bitsVal E)
        (bitsVal (pairFstD z) ^ bitsVal (pairFstD (pairSndD z))))

/-- A residue modulo a positive `p` has a binary word no longer than that of `p`. -/
private theorem length_bits_mod_le (x : ℕ) (w : List Bool) (hw : 0 < bitsVal w) :
    (Nat.bits (x % bitsVal w)).length ≤ w.length :=
  length_bits_le_of_le w (Nat.mod_lt _ hw).le le_rfl

/-- The input state satisfies the repeated-squaring invariant: `(1 mod p)(a mod p)^n ≡ a^n`,
and the reduced words are no longer than `p`'s (or are `a` and `1` when `p = 0`). -/
theorem powInv_init (z : List Bool) : PowInv z (powInit z) := by
  refine ⟨_, _, _, rfl, le_rfl, by simp [mod, bitsVal_bits], by simp [mod, bitsVal_bits], ?_, ?_,
    fun hp => ?_⟩
  · simp only [mod, pairFstD_pairEncode, pairSndD_pairEncode]
    rcases Nat.eq_zero_or_pos (bitsVal (pairSndD (pairSndD z))) with h0 | h0
    · rw [h0, Nat.mod_zero]; have := length_bits_bitsVal_le (pairFstD z); omega
    · have := length_bits_mod_le (bitsVal (pairFstD z)) _ h0; omega
  · simp only [mod, pairFstD_pairEncode, pairSndD_pairEncode]
    rcases Nat.eq_zero_or_pos (bitsVal (pairSndD (pairSndD z))) with h0 | h0
    · rw [h0, Nat.mod_zero]; simp [bitsVal]
    · have := length_bits_mod_le (bitsVal [true]) _ h0; omega
  · simp only [mod, pairFstD_pairEncode, pairSndD_pairEncode, bitsVal_bits]
    refine ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, ?_⟩
    have h := ((Nat.mod_modEq (bitsVal [true]) (bitsVal (pairSndD (pairSndD z)))).mul
      ((Nat.mod_modEq (bitsVal (pairFstD z)) _).pow (bitsVal (pairFstD (pairSndD z)))))
    simpa [bitsVal] using h

/-- The repeated-squaring round preserves the invariant, and for `p ≠ 0` shortens a nonempty
`E`.

**Proof sketch.** Writing `E = c + 2E'`, the round replaces `acc·b^E` by
`(acc·b^c mod p)·(b² mod p)^{E'}`, congruent modulo `p`; the new residues are below `p`, so
their words are no longer than `p`'s. -/
theorem powInv_step {z S : List Bool} (h : PowInv z S) :
    PowInv z (powStep S) ∧
      (0 < bitsVal (pairSndD (pairSndD z)) → 0 < (pairFstD (pairSndD S)).length →
        (pairFstD (pairSndD (powStep S))).length < (pairFstD (pairSndD S)).length) := by
  unfold PowInv at h ⊢
  generalize pairSndD (pairSndD z) = p at h ⊢
  generalize pairFstD (pairSndD z) = n at h ⊢
  generalize pairFstD z = a at h ⊢
  obtain ⟨E, b, acc, rfl, hE, hb, hacc, hbl, haccl, hv⟩ := h
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  by_cases hfix : (isNilB E || decide (bitsVal p = 0)) = true
  · have he : powStep (pairEncode p (pairEncode E (pairEncode b acc))) =
        pairEncode p (pairEncode E (pairEncode b acc)) := by
      simp only [powStep, pairFstD_pairEncode, pairSndD_pairEncode, hfix, if_true]
    rw [he]
    refine ⟨⟨E, b, acc, rfl, hE, hb, hacc, hbl, haccl, hv⟩, fun hp hE0 => ?_⟩
    simp only [isNilB, Bool.or_eq_true, decide_eq_true_eq] at hfix
    rcases hfix with h | h
    · simp [h] at hE0
    · omega
  have hne : E ≠ [] := by simp [isNilB] at hfix; exact hfix.1
  have hp : 0 < bitsVal p := by simp [isNilB] at hfix; exact Nat.pos_of_ne_zero hfix.2
  obtain ⟨c, E', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hstep : powStep (pairEncode p (pairEncode (c :: E') (pairEncode b acc))) =
      pairEncode p (pairEncode E' (pairEncode (Nat.bits (bitsVal b * bitsVal b % bitsVal p))
        (if c then Nat.bits (bitsVal acc * bitsVal b % bitsVal p) else acc))) := by
    rw [Bool.not_eq_true] at hfix
    simp only [powStep, pairFstD_pairEncode, pairSndD_pairEncode, hfix, Bool.false_eq_true,
      if_false, List.drop_succ_cons, List.drop_zero, List.headD_cons, mod, mul, bitsVal_bits]
  rw [hstep]
  refine ⟨?_, fun _ _ => by simp⟩
  obtain ⟨hb1, hacc1, hmod⟩ := hv hp
  refine ⟨E', _, _, rfl, by simp at hE; omega, by simp [bitsVal_bits], ?_, ?_, ?_, fun _ => ?_⟩
  · cases c <;> simp [bitsVal_bits, ← hacc]
  · have := length_bits_mod_le (bitsVal b * bitsVal b) p hp; omega
  · cases c
    · simpa using haccl
    · have := length_bits_mod_le (bitsVal acc * bitsVal b) p hp; simp; omega
  · refine ⟨by simp [bitsVal_bits, Nat.mod_lt _ hp], ?_, ?_⟩
    · cases c <;> simp [bitsVal_bits, Nat.mod_lt _ hp, hacc1]
    · have hsq := (Nat.mod_modEq (bitsVal b * bitsVal b) (bitsVal p)).pow (bitsVal E')
      refine Nat.ModEq.trans ?_ hmod
      rw [bitsVal_bits]
      cases c
      · have := (Nat.ModEq.refl (n := bitsVal p) (bitsVal acc)).mul hsq
        refine this.trans (congrArg (· % bitsVal p) ?_)
        simp only [bitsVal, Bool.toNat_false, zero_add, pow_mul, ← pow_two]
      · have := (Nat.mod_modEq (bitsVal acc * bitsVal b) (bitsVal p)).mul hsq
        simp only [if_true, bitsVal_bits]
        refine this.trans (congrArg (· % bitsVal p) ?_)
        simp only [bitsVal, Bool.toNat_true, pow_add, pow_mul, ← pow_two]; ring

/-- A state satisfying the repeated-squaring invariant has length at most `9(|z| + 1)`. -/
theorem length_le_of_powInv {z S : List Bool} (h : PowInv z S) :
    S.length ≤ 9 * (z.length + 1) := by
  obtain ⟨E, b, acc, rfl, hE, -, -, hbl, haccl, -⟩ := h
  have h1 := length_pair_components_le z
  have h2 := length_pair_components_le (pairSndD z)
  simp only [length_pairEncode]
  omega

/-- The repeated-squaring loop: `|z| + 1` rounds from `powInit z`. -/
def powLoop (z : List Bool) : List Bool := powStep^[1 * (z.length + 1) ^ 1] (powInit z)

/-- **Modular exponentiation is polynomial-time** [AB09, Exercise 7.3]: given `a, n, p` in
binary, `a^n mod p` is computable in polynomial time.

**Proof sketch.** Repeated squaring from `⟨p, ⟨n, ⟨a mod p, 1 mod p⟩⟩⟩` keeps
`acc · b^E ≡ a^n (mod p)` with `acc, b < p` (`PowInv`), so states stay linear in length; each
round removes the low bit of `E`, so after `|z| + 1` rounds `E = []` and `acc = a^n mod p`.
The case `p = 0` is answered directly. -/
theorem polyTimeComputable_powMod : PolyTimeComputable powMod := by
  have hinit : PolyTimeComputable powInit :=
    polyTimeComputable_slot3.pairEncode
      ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
        ((polyTimeComputable_mod.comp
          (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot3)).pairEncode
          (polyTimeComputable_mod.comp
            ((polyTimeComputable_const [true]).pairEncode polyTimeComputable_slot3))))
  have hloop : PolyTimeComputable powLoop :=
    polyTimeComputable_iterate polyTimeComputable_powStep hinit 1 1 9 1 (fun z i _ => by
      simpa using length_le_of_powInv
        (iterate_invariant (PowInv z) (fun _ h => (powInv_step h).1) i (powInv_init z)))
  convert polyTimeComputable_ite (polyTimeComputable_isZero.comp polyTimeComputable_slot3)
    (polyTimeComputable_const []) (polyTimeComputable_slot4.comp hloop) using 1
  funext z
  simp only [Function.comp_apply, powMod]
  by_cases hp : bitsVal (pairSndD (pairSndD z)) = 0
  · simp [hp, Nat.zero_bits]
  simp only [hp, decide_false, Bool.false_eq_true, if_false]
  have hμ := iterate_measure_eq_zero (g := powStep) (PowInv z)
    (fun S => (pairFstD (pairSndD S)).length) (fun _ h => (powInv_step h).1)
    (fun S h hpos => (powInv_step h).2 (Nat.pos_of_ne_zero hp) hpos)
    (fun S h h0 => by
      obtain ⟨E, b, acc, rfl, -⟩ := h
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_eq_zero_iff] at h0
      subst h0; simp [powStep, isNilB])
    (1 * (z.length + 1) ^ 1) (powInit z) (powInv_init z)
    (by simp [powInit]; have := length_pairFstD_le (pairSndD z)
        have := length_pairSndD_le z; omega)
  obtain ⟨E, b, acc, he, -, -, hacc, -, -, hv⟩ :=
    iterate_invariant (PowInv z) (fun _ h => (powInv_step h).1) (1 * (z.length + 1) ^ 1)
      (powInv_init z)
  rw [powLoop, he]
  rw [he] at hμ
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_eq_zero_iff] at hμ ⊢
  subst hμ
  obtain ⟨-, hacc1, hmod⟩ := hv (Nat.pos_of_ne_zero hp)
  simp only [bitsVal, pow_zero, mul_one] at hmod
  rw [hacc, ← Nat.mod_eq_of_lt hacc1, hmod]

/-! ### The gcd -/

/-- The gcd of the values of the two components of `z`, as a binary word. -/
def gcd (z : List Bool) : List Bool :=
  Nat.bits (Nat.gcd (bitsVal (pairFstD z)) (bitsVal (pairSndD z)))

/-- `gcd` on encoded numbers is `Nat.gcd`. -/
@[simp] theorem gcd_pairEncode (a b : ℕ) :
    gcd (pairEncode (Nat.bits a) (Nat.bits b)) = Nat.bits (Nat.gcd a b) := by
  simp [gcd, bitsVal_bits]

/-- One Euclid round on `⟨x, y⟩`: `⟨y, x mod y⟩`; states with `y = 0` are fixed. -/
def gcdStep (S : List Bool) : List Bool :=
  if decide (bitsVal (pairSndD S) = 0) then S
  else pairEncode (pairSndD S) (mod (pairEncode (pairFstD S) (pairSndD S)))

/-- A Euclid round is polynomial-time. -/
theorem polyTimeComputable_gcdStep : PolyTimeComputable gcdStep := by
  unfold gcdStep
  exact polyTimeComputable_ite (polyTimeComputable_isZero.comp polyTimeComputable_pairSndD)
    polyTimeComputable_id (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_mod.comp
      (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD)))

/-- The invariant of Euclid's loop on `z = ⟨a, b⟩`: the state is a pair of words no longer
than `z` whose values have gcd `gcd(a, b)`. -/
def GcdInv (z S : List Bool) : Prop :=
  ∃ x y, S = pairEncode x y ∧ x.length ≤ z.length ∧ y.length ≤ z.length ∧
    Nat.gcd (bitsVal x) (bitsVal y) = Nat.gcd (bitsVal (pairFstD z)) (bitsVal (pairSndD z))

/-- The potential of Euclid's loop: the bit size of `x·y`, plus one while `x < y`. -/
def gcdMeasure (S : List Bool) : ℕ :=
  Nat.size (bitsVal (pairFstD S) * bitsVal (pairSndD S)) +
    if bitsVal (pairFstD S) < bitsVal (pairSndD S) then 1 else 0

/-- Halving a positive number lowers its bit size. -/
theorem size_lt_of_two_mul_le {P P' : ℕ} (hP : 0 < P) (h : 2 * P' ≤ P) :
    Nat.size P' < Nat.size P := by
  have h1 := Nat.lt_size_self P
  have h2 : 0 < Nat.size P := Nat.size_pos.mpr hP
  have h3 : P' < 2 ^ (Nat.size P - 1) := by
    have : 2 ^ Nat.size P = 2 * 2 ^ (Nat.size P - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have := Nat.size_le.mpr h3
  omega

/-- The Euclid round preserves the invariant, strictly lowers the potential of a state with
`y ≠ 0`, and fixes states with potential `0`.

**Proof sketch.** `gcd(y, x mod y) = gcd(x, y)` (`Nat.gcd_rec`). If `x < y` the round only
swaps, and the flag drops; otherwise `x = qy + r` with `q ≥ 1` gives `2r ≤ x`, so the product
`y·r` is at most half of `x·y` and its bit size drops (`size_lt_of_two_mul_le`). -/
theorem gcdInv_step {z S : List Bool} (h : GcdInv z S) :
    GcdInv z (gcdStep S) ∧ (0 < gcdMeasure S → gcdMeasure (gcdStep S) < gcdMeasure S) ∧
      (gcdMeasure S = 0 → gcdStep S = S) := by
  obtain ⟨x, y, rfl, hx, hy, hg⟩ := h
  simp only [gcdMeasure, gcdStep, pairFstD_pairEncode, pairSndD_pairEncode]
  by_cases hy0 : bitsVal y = 0
  · simp only [hy0, decide_true, if_true]
    exact ⟨⟨x, y, rfl, hx, hy, hg⟩, fun h => by simp at h, fun _ => trivial⟩
  have hypos := Nat.pos_of_ne_zero hy0
  simp only [hy0, decide_false, Bool.false_eq_true, if_false, mod, pairFstD_pairEncode,
    pairSndD_pairEncode, bitsVal_bits]
  have hlt := Nat.mod_lt (bitsVal x) hypos
  refine ⟨⟨y, _, rfl, hy, ?_, ?_⟩, fun _ => ?_, fun h0 => ?_⟩
  · exact (length_bits_le_of_le y hlt.le le_rfl).trans hy
  · simp only [bitsVal_bits]
    rw [← hg, Nat.gcd_comm (bitsVal x) (bitsVal y), Nat.gcd_rec (bitsVal y) (bitsVal x),
      Nat.gcd_comm]
  · simp only [Nat.not_lt.mpr hlt.le, if_false, add_zero]
    by_cases hxy : bitsVal x < bitsVal y
    · rw [Nat.mod_eq_of_lt hxy, if_pos hxy, Nat.mul_comm]; omega
    · rw [if_neg hxy, add_zero]
      apply size_lt_of_two_mul_le (Nat.mul_pos (by omega) hypos)
      have h1 := Nat.div_add_mod (bitsVal x) (bitsVal y)
      have h2 : 1 ≤ bitsVal x / bitsVal y := (Nat.one_le_div_iff hypos).mpr (by omega)
      have h3 : 2 * (bitsVal x % bitsVal y) ≤ bitsVal x := by nlinarith
      nlinarith
  · exfalso
    have hs := Nat.size_eq_zero.mp (by omega : Nat.size (bitsVal x * bitsVal y) = 0)
    have : ¬ bitsVal x < bitsVal y := by intro h; simp [h] at h0
    rcases Nat.mul_eq_zero.mp hs with h | h <;> omega

/-- Euclid's loop: `2(|z| + 1)` rounds from `⟨a, b⟩`. -/
def gcdLoop (z : List Bool) : List Bool :=
  gcdStep^[2 * (z.length + 1) ^ 1] (pairEncode (pairFstD z) (pairSndD z))

/-- **The gcd is polynomial-time** (infrastructure for [AB09 §7.2.2]; not itself a result of
the book).

**Proof sketch.** Euclid's rounds `⟨x, y⟩ ↦ ⟨y, x mod y⟩` keep the gcd and shrink the words
(`GcdInv`). The potential `size(x·y) + [x < y]` drops on every round with `y ≠ 0`: a round
with `x < y` swaps, and otherwise `x mod y ≤ x / 2` halves the product. It starts at most
`|z| + 1`, so after `2(|z| + 1)` rounds `y = 0` and `x` has value `gcd(a, b)`. -/
theorem polyTimeComputable_gcd : PolyTimeComputable gcd := by
  have hinit : PolyTimeComputable (fun z => pairEncode (pairFstD z) (pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD
  have h0 : ∀ z : List Bool, GcdInv z (pairEncode (pairFstD z) (pairSndD z)) := fun z =>
    ⟨_, _, rfl, length_pairFstD_le z, length_pairSndD_le z, rfl⟩
  have hloop : PolyTimeComputable gcdLoop :=
    polyTimeComputable_iterate polyTimeComputable_gcdStep hinit 2 1 3 1 (fun z i _ => by
      obtain ⟨x, y, he, hx, hy, -⟩ :=
        iterate_invariant (GcdInv z) (fun _ h => (gcdInv_step h).1) i (h0 z)
      rw [he, length_pairEncode]; simp; omega)
  convert polyTimeComputable_normBits.comp (polyTimeComputable_pairFstD.comp hloop) using 1
  funext z
  have hμ := iterate_measure_eq_zero (g := gcdStep) (GcdInv z) gcdMeasure
    (fun _ h => (gcdInv_step h).1) (fun _ h => (gcdInv_step h).2.1)
    (fun _ h => (gcdInv_step h).2.2) (2 * (z.length + 1) ^ 1) _ (h0 z) (by
      simp only [gcdMeasure, pairFstD_pairEncode, pairSndD_pairEncode, pow_one]
      have hs : Nat.size (bitsVal (pairFstD z) * bitsVal (pairSndD z)) ≤ z.length := by
        rw [Nat.size_le]
        calc bitsVal (pairFstD z) * bitsVal (pairSndD z)
            < 2 ^ (pairFstD z).length * 2 ^ (pairSndD z).length := by
              rcases Nat.eq_zero_or_pos (bitsVal (pairSndD z)) with h0 | h0
              · rw [h0, mul_zero]; positivity
              · exact Nat.mul_lt_mul_of_lt_of_le (bitsVal_lt_two_pow _)
                  (bitsVal_lt_two_pow _).le (by positivity)
          _ ≤ 2 ^ z.length := by
              rw [← pow_add]; apply Nat.pow_le_pow_right (by norm_num)
              have := length_pair_components_le z; omega
      split_ifs <;> omega)
  obtain ⟨x, y, he, -, -, hg⟩ :=
    iterate_invariant (GcdInv z) (fun _ h => (gcdInv_step h).1) (2 * (z.length + 1) ^ 1) (h0 z)
  rw [he] at hμ
  simp only [gcdMeasure, pairFstD_pairEncode, pairSndD_pairEncode] at hμ
  have hy : bitsVal y = 0 := by
    have hs := Nat.size_eq_zero.mp (by omega : Nat.size (bitsVal x * bitsVal y) = 0)
    have : ¬ bitsVal x < bitsVal y := by intro h; simp [h] at hμ
    rcases Nat.mul_eq_zero.mp hs with h | h <;> omega
  simp only [Function.comp_apply, gcdLoop, he, pairFstD_pairEncode, gcd, ← hg, hy,
    Nat.gcd_zero_right]

end BinArith

end Complexity
