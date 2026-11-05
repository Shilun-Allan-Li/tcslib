/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMWidth
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exhaustive search with a polynomially wide register

A non-vacuity check for `Complexity.LogProg.arm_decides_pspace_val`, on an algorithm that
genuinely needs registers of more than logarithmically many binary digits: for a language
`P ∈ PSPACE`, the language `Complexity.LogProg.WidthExample.searchLang P` of inputs `x` having
a witness `u < 2^|x|` with `⟨x, bits u⟩ ∈ P` is in `PSPACE`. The abstract register machine
`Complexity.LogProg.WidthExample.searchA` measures `n = |x|` (asking the logspace decider of
`Complexity.inputLenLang`), computes `2^n` by `n` doublings, and then runs a counter `u`
through `0, 1, …, 2^n - 1`, asking the decider of `P` on `⟨x, bits u⟩`. The counter and the
bound `2^n` have `n + 1` binary digits — far beyond the `O(log n)` of
`Complexity.LogProg.arm_decides`.

## Main definitions

* `Complexity.LogProg.WidthExample.searchLang` — exhaustive search over `|x|`-bit witnesses.
* `Complexity.LogProg.WidthExample.searchA` — the search machine.

## Main results

* `Complexity.LogProg.WidthExample.searchLang_mem_PSPACE` — `searchLang P ∈ PSPACE` for
  `P ∈ PSPACE`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; compare the exhaustive-search argument of
  Example 4.6, `NP ⊆ PSPACE`.)
-/

namespace Complexity.LogProg

namespace WidthExample

open Turing

/-- **Exhaustive search over `|x|`-bit witnesses**: the inputs `x` with some `u < 2^|x|` such
that `⟨x, bits u⟩ ∈ P`. -/
def searchLang (P : Language Bool) : Language Bool :=
  {x | ∃ u < 2 ^ x.length, pairEncode x (Nat.bits u) ∈ P}

/-- The labels of the search machine. -/
inductive Lb where
  | init | scan | incI | dbl | decI | d1 | d1a | d1b | d1c | d2 | d2a | d2b
  | enum | chk | nxt | acc | rej
  deriving DecidableEq, Fintype

/-- **The search machine**, on registers `i = 0`, `p = 1`, `t = 2`, `u = 3`: set `p = 1`;
count `i = |x|` (asking `i < |x|` of decider `0`); while `i ≠ 0`, decrement `i` and double `p`
(move `p` into `t` twice over, then back); finally, for `u = 0, 1, …` until `u = p = 2^|x|`,
accept if decider `1` accepts `⟨x, bits u⟩`; reject at the end. -/
def searchA : ARM 4 2 Lb
  | .init => .inc 1 .scan
  | .scan => .call 0 .whole [0] .incI .dbl
  | .incI => .inc 0 .scan
  | .dbl => .jz 0 .enum .decI
  | .decI => .dec 0 .d1
  | .d1 => .jz 1 .d2 .d1a
  | .d1a => .dec 1 .d1b
  | .d1b => .inc 2 .d1c
  | .d1c => .inc 2 .d1
  | .d2 => .jz 2 .dbl .d2a
  | .d2a => .dec 2 .d2b
  | .d2b => .inc 1 .d2
  | .enum => .jeq 3 1 .rej .chk
  | .chk => .call 1 .whole [3] .acc .nxt
  | .nxt => .inc 3 .enum
  | .acc => .ret true
  | .rej => .ret false

/-- The deciders: `0` is `Complexity.inputLenLang` (`i < |x|`), `1` is `P`. -/
def decs (P : Language Bool) : Fin 2 → Language Bool := ![inputLenLang, P]

/-- The oracle: membership in the deciders' languages. -/
noncomputable def orc (P : Language Bool) : Fin 2 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (decs P j : Set (List Bool)) V

/-- The register file `(i, p, t, u)`. -/
def rf (i p t u : ℕ) : Fin 4 → ℕ := ![i, p, t, u]

/-- Updating register `0` (`i`) of the register file. -/
@[simp] lemma rf_upd0 (i p t u a : ℕ) : Function.update (rf i p t u) 0 a = rf a p t u := by
  funext k
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  | ⟨_ + 4, h⟩ => omega
/-- Updating register `1` (`p`) of the register file. -/
@[simp] lemma rf_upd1 (i p t u a : ℕ) : Function.update (rf i p t u) 1 a = rf i a t u := by
  funext k
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  | ⟨_ + 4, h⟩ => omega
/-- Updating register `2` (`t`) of the register file. -/
@[simp] lemma rf_upd2 (i p t u a : ℕ) : Function.update (rf i p t u) 2 a = rf i p a u := by
  funext k
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  | ⟨_ + 4, h⟩ => omega
/-- Updating register `3` (`u`) of the register file. -/
@[simp] lemma rf_upd3 (i p t u a : ℕ) : Function.update (rf i p t u) 3 a = rf i p t a := by
  funext k
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  | ⟨_ + 4, h⟩ => omega
/-- Register `0` of the register file is `i`. -/
@[simp] lemma rf_0 (i p t u : ℕ) : rf i p t u 0 = i := rfl
/-- Register `1` of the register file is `p`. -/
@[simp] lemma rf_1 (i p t u : ℕ) : rf i p t u 1 = p := rfl
/-- Register `2` of the register file is `t`. -/
@[simp] lemma rf_2 (i p t u : ℕ) : rf i p t u 2 = t := rfl
/-- Register `3` of the register file is `u`. -/
@[simp] lemma rf_3 (i p t u : ℕ) : rf i p t u 3 = u := rfl

/-- The guard of the runs: the syntactic preconditions, and every register at most `B`. -/
def G (x : List Bool) (B : ℕ) : AConf 4 Lb → Prop :=
  fun a => PreS searchA x a ∧ ∀ s, a.2.1 s ≤ B

/-- Every configuration of the search machine with registers at most `B` meets the guard. -/
lemma guard_rf (x : List Bool) (B : ℕ) (l : Lb) {i p t u : ℕ} (hi : i ≤ B) (hp : p ≤ B) (ht : t ≤ B)
    (hu : u ≤ B) : G x B (some l, rf i p t u, none) := by
  refine ⟨by cases l <;> simp [PreS, searchA], fun s => ?_⟩
  match s with
  | ⟨0, _⟩ => exact hi
  | ⟨1, _⟩ => exact hp
  | ⟨2, _⟩ => exact ht
  | ⟨3, _⟩ => exact hu
  | ⟨_ + 4, h⟩ => omega

variable (P : Language Bool) (x : List Bool) (B : ℕ)

/-- **The first half of a doubling**: from `d1` with `p = a`, `t = b`, the machine moves `p`
into `t` twice over, reaching `d2` with `p = 0`, `t = b + 2a`.

**Proof sketch.** Induction on `a`: each round decrements `p` and increments `t` twice. -/
lemma d1_loop (i u : ℕ) (hi : i ≤ B) (hu : u ≤ B) : ∀ a b, b + 2 * a ≤ B →
    AReach searchA (orc P) x (G x B) (some .d1, rf i a b u, none)
      (some .d2, rf i 0 (b + 2 * a) u, none) := by
  intro a
  induction a with
  | zero =>
    intro b hb
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simpa [astep, searchA] using AReach.refl _
  | succ a ih =>
    intro b hb
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simp only [astep, searchA, rf_1, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simp only [astep, searchA, rf_1, rf_upd1, Nat.add_sub_cancel]
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simp only [astep, searchA, rf_2, rf_upd2]
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simp only [astep, searchA, rf_2, rf_upd2]
    have e : b + 2 * (a + 1) = b + 1 + 1 + 2 * a := by ring
    rw [e]
    exact ih (b + 1 + 1) (by omega)

/-- **The second half of a doubling**: from `d2` with `p`, `t = b`, the machine moves `t`
back into `p`, reaching `dbl` with `p + b` and `t = 0`.

**Proof sketch.** Induction on `b`: each round decrements `t` and increments `p`. -/
lemma d2_loop (i u : ℕ) (hi : i ≤ B) (hu : u ≤ B) : ∀ b p, p + b ≤ B →
    AReach searchA (orc P) x (G x B) (some .d2, rf i p b u, none)
      (some .dbl, rf i (p + b) 0 u, none) := by
  intro b
  induction b with
  | zero =>
    intro p hb
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simpa [astep, searchA] using AReach.refl _
  | succ b ih =>
    intro p hb
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simp only [astep, searchA, rf_2, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simp only [astep, searchA, rf_2, rf_upd2, Nat.add_sub_cancel]
    refine AReach.step (guard_rf x B _ hi (by omega) (by omega) hu) ?_
    simp only [astep, searchA, rf_1, rf_upd1]
    have e : p + (b + 1) = p + 1 + b := by ring
    rw [e]
    exact ih (p + 1) (by omega)

/-- **The doubling loop**: from `dbl` with `i = k`, `p = 2^a` and `a + k = n`, `2^n ≤ B`, the
machine reaches `enum` with `i = 0`, `p = 2^n`.

**Proof sketch.** Induction on `k`: each round decrements `i` and doubles `p` (`d1_loop`,
`d2_loop`), all registers staying at most `2^n`. -/
lemma dbl_loop (n : ℕ) (hB : 2 ^ n ≤ B) : ∀ k a, a + k = n →
    AReach searchA (orc P) x (G x B) (some .dbl, rf k (2 ^ a) 0 0, none)
      (some .enum, rf 0 (2 ^ n) 0 0, none) := by
  have hn : n ≤ B := (Nat.lt_two_pow_self).le.trans hB
  intro k
  induction k with
  | zero =>
    intro a ha
    obtain rfl : a = n := by omega
    refine AReach.step (guard_rf x B _ (by omega) hB (by omega) (by omega)) ?_
    simpa [astep, searchA] using AReach.refl _
  | succ k ih =>
    intro a ha
    have h2 : 2 ^ (a + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e2 : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    refine AReach.step (guard_rf x B _ (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [astep, searchA, rf_0, Nat.add_one_ne_zero, ↓reduceIte]
    refine AReach.step (guard_rf x B _ (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [astep, searchA, rf_0, rf_upd0, Nat.add_sub_cancel]
    refine (d1_loop P x B k 0 (by omega) (by omega) (2 ^ a) 0 (by omega)).trans ?_
    refine (d2_loop P x B k 0 (by omega) (by omega) (0 + 2 * 2 ^ a) 0 (by omega)).trans ?_
    have e : 0 + (0 + 2 * 2 ^ a) = 2 ^ (a + 1) := by omega
    rw [e]
    exact ih (a + 1) (by omega)

/-- **The search loop**: from `enum` with `p = 2^n` and counter `u ≤ 2^n`, `2^n ≤ B`, the
machine answers whether some `w` with `u ≤ w < 2^n` has `⟨x, bits w⟩ ∈ P`.

**Proof sketch.** Induction on `2^n - u`. At `u = 2^n` the machine rejects, and no such `w`
exists. Below, it accepts if `⟨x, bits u⟩ ∈ P`, and otherwise moves to `u + 1`. -/
lemma enum_loop (n : ℕ) (hB : 2 ^ n ≤ B) : ∀ k u, u + k = 2 ^ n → ∀ b : Bool,
    (b = true ↔ ∃ w, u ≤ w ∧ w < 2 ^ n ∧ pairEncode x (Nat.bits w) ∈ P) →
    AHalt searchA (orc P) x (G x B) (some .enum, rf 0 (2 ^ n) 0 u, none) b := by
  intro k
  induction k with
  | zero =>
    intro u hu b hb
    obtain rfl : u = 2 ^ n := by omega
    refine AHalt.step (guard_rf x B _ (by omega) hB (by omega) hB) ?_
    simp only [astep, searchA, rf_1, rf_3, ↓reduceIte]
    obtain rfl : b = false := by
      cases b
      · rfl
      · obtain ⟨w, h1, h2, -⟩ := hb.mp rfl; omega
    exact AHalt.ret rfl (guard_rf x B _ (by omega) hB (by omega) hB)
  | succ k ih =>
    intro u hu b hb
    have hu' : u < 2 ^ n := by omega
    refine AHalt.step (guard_rf x B _ (by omega) hB (by omega) (by omega)) ?_
    simp only [astep, searchA, rf_1, rf_3, hu'.ne, ↓reduceIte]
    refine AHalt.step (guard_rf x B _ (by omega) hB (by omega) (by omega)) ?_
    have ho : orc P 1 (pairEncode x (Nat.bits u)) = true ↔ pairEncode x (Nat.bits u) ∈ P := by
      simp [orc, decs, indicator_eq_decide]
    simp only [astep, searchA, vword_whole₁, rf_3]
    by_cases hq : pairEncode x (Nat.bits u) ∈ P
    · rw [if_pos (ho.mpr hq)]
      obtain rfl : b = true := hb.mpr ⟨u, le_rfl, hu', hq⟩
      exact AHalt.ret rfl (guard_rf x B _ (by omega) hB (by omega) (by omega))
    · have hf : orc P 1 (pairEncode x (Nat.bits u)) = false := by
        simpa using mt ho.mp hq
      rw [hf]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine AHalt.step (guard_rf x B _ (by omega) hB (by omega) (by omega)) ?_
      simp only [astep, searchA, rf_3, rf_upd3]
      refine ih (u + 1) (by omega) b (hb.trans ⟨fun ⟨w, h1, h2, h3⟩ => ⟨w, ?_, h2, h3⟩,
        fun ⟨w, h1, h2, h3⟩ => ⟨w, by omega, h2, h3⟩⟩)
      rcases Nat.lt_or_ge u w with h | h
      · omega
      · obtain rfl : w = u := by omega
        exact absurd h3 hq

/-- **Exhaustive search over `|x|`-bit witnesses preserves `PSPACE`**: if `P ∈ PSPACE` then
the language of inputs `x` with some `u < 2^|x|` such that `⟨x, bits u⟩ ∈ P` is in
`PSPACE`. [AB09, §4.1; the exhaustive-search argument of Example 4.6] — here an example of
`Complexity.LogProg.arm_decides_pspace_val`, whose registers hold values up to `2^|x|`.

**Proof sketch.** `Complexity.LogProg.arm_decides_pspace_val` with the deciders of
`Complexity.inputLenLang` (in `L ⊆ PSPACE`) and `P`, and value bound `2^{|x| + 1}`. The
machine sets `p = 1`, counts `i = |x|` (`Complexity.LogProg.inputLength_loop`), doubles `p`
`|x|` times (`dbl_loop`), and searches `u = 0, …, 2^|x| - 1` (`enum_loop`); every register
stays at most `2^|x|`. -/
theorem searchLang_mem_PSPACE (hP : P ∈ PSPACE) : searchLang P ∈ PSPACE := by
  refine arm_decides_pspace_val searchA .init (decs P) (fun j => ?_) 1 1 fun x => ?_
  · match j with
    | 0 => exact LOGSPACE_subset_PSPACE inputLenLang_mem
    | 1 => exact hP
  set n := x.length with hn
  set B := 2 ^ (1 * (x.length + 1) ^ 1) with hB'
  have hB : 2 ^ n ≤ B := Nat.pow_le_pow_right (by norm_num) (by rw [pow_one, one_mul]; omega)
  have hnB : n ≤ B := (Nat.lt_two_pow_self).le.trans hB
  have h1B : 1 ≤ B := Nat.one_le_two_pow
  -- `init`: set `p = 1`
  have e0 : (fun _ : Fin 4 => 0) = rf 0 0 0 0 := by
    funext k
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
    | ⟨_ + 4, h⟩ => omega
  rw [e0]
  refine AHalt.step (G := G x B) (guard_rf x B (i := 0) (p := 0) (t := 0) (u := 0) .init
    (by omega) (by omega) (by omega) (by omega)) ?_
  simp only [astep, searchA, rf_1, rf_upd1, zero_add]
  -- count `i = |x|`
  have hq : ∀ k ≤ x.length, orc P 0 (pairEncode x (Nat.bits k)) = decide (k < x.length) := by
    intro k _
    simp only [orc, decs, Matrix.cons_val_zero, inputLenLang, indicator_indexLang_pairEncode]
    exact decide_eq_decide.mpr Iff.rfl
  have hcount := inputLength_loop searchA (orc P) x 0 0 .scan .incI .dbl rfl rfl hq B
    (by omega) (rf 0 1 0 0) (fun s => (guard_rf x B .init (by omega) h1B (by omega) (by omega)).2 s)
    (by simp)
  simp only [rf_upd0] at hcount
  refine hcount.halt ?_
  -- double `p` `|x|` times, then search
  have hd := dbl_loop P x B n hB n 0 (by omega)
  rw [pow_zero] at hd
  refine hd.halt (enum_loop P x B n hB (2 ^ n) 0 (by omega) _ ?_)
  simp [indicator_eq_decide, searchLang, hn]

end WidthExample

end Complexity.LogProg
