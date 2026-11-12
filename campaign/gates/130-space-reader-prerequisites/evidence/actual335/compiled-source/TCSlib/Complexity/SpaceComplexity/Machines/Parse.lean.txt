/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ParsePlain

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments reading the input

Logspace programs cannot copy their input into work space; they read it in place. This file
provides the input-reading fragments of register-tape programs whose inputs have the shape
`⟨1ⁿ, w⟩` (`Turing.pairEncode (1ⁿ) w`, i.e. `1²ⁿ 0 1 w`) or `⟨1ⁿ, ⟨u, w⟩⟩`:

* the *format checks* `valPlain`/`valPair` accept exactly the inputs of that shape whose
  binary components have no trailing `0` (the words `Nat.bits i`), and otherwise reject
  (write `0` and halt);
* the *comparisons* test whether a register's counter equals the index written on the input,
  walking the register and the input in lockstep — no copying.

The input shapes, input-scanning configurations and the plain format check are in
`TCSlib.Complexity.SpaceComplexity.Machines.ParsePlain`, which this file re-exports; this file
has the comparison of a register with the index of a plain input (`jeqPlain_run`).

## Main definitions

* `Complexity.LogProg.ValidPlain`, `Complexity.LogProg.ValidPair` — the input shapes.
* `Complexity.LogProg.xCfg` — a configuration with the input head and one register head
  moved.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1: logspace machines read their input in place.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-! ## Comparing a register with the index on the input -/

/-- A word without trailing `0` is the binary word of its value. -/
lemma canon_eq_bits (w : List Bool) (h : Canon w) : w = Nat.bits (bitsVal w) := by
  induction w with
  | nil => simp [bitsVal, Nat.zero_bits]
  | cons b w ih =>
    have hw := ih (canon_tail h)
    simp only [bitsVal]
    rw [show b.toNat + 2 * bitsVal w = 2 * bitsVal w + b.toNat by ring,
      bits_two_mul_add _ _ (fun h0 => ?_), ← hw]
    -- `w = []`: then `b` is the last bit
    have : w = [] := by
      rw [hw, h0]; simp [Nat.zero_bits]
    subst this
    simpa using h (by simp)

/-- The return walk of a register in an input fragment: left over the word, then onto cell
`0`.

**Proof sketch.** Induction on `n = q + 1`: on a letter of the register word the register head
moves left; at the left blank it moves right onto cell `0` and the state becomes `nx`. The input
head never moves. -/
lemma regBack_x (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (r : Fin m) (w : List Bool) (hw : c.workTapes r = FinTM.bufferTape w) (s₀ nx : Λ)
    (htr : ∀ a ww, P.tm.tr s₀ a ww = match ww r with
      | some _ => xAct r 0 (-1) s₀
      | none => xAct r 0 1 nx)
    (hc : P.call s₀ = none) (ip : Fin (x.length + 2)) :
    ∀ (n : ℕ) (q : ℤ), q + 1 = n → q < w.length →
      rrun P oracle (xCfg c s₀ ip r q) (n + 1) = xCfg c nx ip r 0 ∧
      ∀ t < n + 1, ∃ q', rrun P oracle (xCfg c s₀ ip r q) t = xCfg c s₀ ip r q' ∧
        -1 ≤ q' ∧ q' ≤ q := by
  intro n
  induction n with
  | zero =>
    intro q hq _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨q, rfl, by omega, le_rfl⟩
    rw [rrun_one_x P oracle c s₀ ip r q hc, htr, xCfg_read, hw]
    have hrd : FinTM.bufferTape w q = none := by rw [show q = -1 by omega]; simp
    rw [hrd]
    simp only
    rw [apply_xAct]
    congr 1; simp
  | succ n ih =>
    intro q hq hqw
    obtain ⟨j, hj⟩ : ∃ j : ℕ, q = j := ⟨q.toNat, by omega⟩
    have hjw : j < w.length := by omega
    have hstep : rrun P oracle (xCfg c s₀ ip r q) 1 = xCfg c s₀ ip r (q - 1) := by
      rw [rrun_one_x P oracle c s₀ ip r q hc, htr, xCfg_read, hw]
      have hrd : FinTM.bufferTape w q = some w[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only
      rw [apply_xAct]
      simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (q - 1) (by omega) (by omega)
    refine ⟨by rw [rrun_succ_left, hstep, ihr], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨q, rfl, by omega, le_rfl⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      rw [rrun_add, hstep]
      obtain ⟨q', hq', h1, h2⟩ := ihm t' (by omega)
      exact ⟨q', hq', h1, by omega⟩

/-- Skip the run of `1`s and the separator `0`. -/
def skipAct (r : Fin m) (jK jK2 : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 jK
  | _ => xAct r 1 0 jK2

/-- Compare the input symbol `a` with the register symbol `c`. -/
def cmpAct (r : Fin m) (jC : Λ) (jRB : Bool → Λ) (a c : Option Bool) : Action m Bool Λ :=
  if a = c then (if a = none then xAct r 0 (-1) (jRB true) else xAct r 1 1 jC)
  else xAct r 0 (-1) (jRB false)

/-- The register return of a comparison. -/
def backAct (r : Fin m) (s₀ nx : Λ) (c : Option Bool) : Action m Bool Λ :=
  match c with
  | some _ => xAct r 0 (-1) s₀
  | none => xAct r 0 1 nx

/-- The input rewind of a comparison: scan. -/
def rewAct (r : Fin m) (s₀ nx : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some _ => xAct r (-1) 0 s₀
  | none => xAct r 1 0 nx

section JeqPlain

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (jK jK2 jC : Λ) (jRB jI1 jI2 : Bool → Λ) (yes no : Λ)
  (hK : ∀ a w, P.tm.tr jK a w = skipAct r jK jK2 a)
  (hK2 : ∀ a w, P.tm.tr jK2 a w = xAct r 1 0 jC)
  (hC : ∀ a w, P.tm.tr jC a w = cmpAct r jC jRB a (w r))
  (hRB : ∀ b a w, P.tm.tr (jRB b) a w = backAct r (jRB b) (jI1 b) (w r))
  (hI1 : ∀ b a w, P.tm.tr (jI1 b) a w = xAct r (-1) 0 (jI2 b))
  (hI2 : ∀ b a w, P.tm.tr (jI2 b) a w = rewAct r (jI2 b) (if b then yes else no) a)
  (cK : P.call jK = none) (cK2 : P.call jK2 = none) (cC : P.call jC = none)
  (cRB : ∀ b, P.call (jRB b) = none) (cI1 : ∀ b, P.call (jI1 b) = none)
  (cI2 : ∀ b, P.call (jI2 b) = none)

include hRB hI1 hI2 cRB cI1 cI2 in
/-- **The return after a comparison** that decided `b` with the register head at `k - 1`: the
register head walks back to cell `0` and the input head to position `1`, ending in `yes` or `no`
according to `b`.

**Proof sketch.** Walk the register head back (`regBack_x`), then rewind the input head
(`rewind_x`), and concatenate the runs (`rrun_add`). The register head stays in `[-1, k - 1]`
during the first walk and at `0` during the second. -/
lemma cmpReturn (c : Cfg m Bool Λ x) (wr : List Bool) (hw : c.workTapes r = FinTM.bufferTape wr)
    (b : Bool) (ip : Fin (x.length + 2)) (k : ℤ) (hk0 : 0 ≤ k) (hk : k ≤ wr.length) :
    ∃ T, rrun P oracle (xCfg c (jRB b) ip r (k - 1)) T =
        xCfg c (if b then yes else no) ⟨1, by omega⟩ r 0 ∧
      ∀ t < T, ∃ s ip' q, rrun P oracle (xCfg c (jRB b) ip r (k - 1)) t = xCfg c s ip' r q ∧
        P.call s = none ∧ -1 ≤ q ∧ q ≤ wr.length := by
  obtain ⟨h1, hm1⟩ := regBack_x P oracle c r wr hw (jRB b) (jI1 b)
    (fun a ww => by rw [hRB]; simp only [backAct]) (cRB b) ip k.toNat (k - 1)
    (by omega) (by omega)
  have hrw := rewind_x P oracle c r 0 (jI1 b) (jI2 b) (if b then yes else no) (hI1 b)
    (fun a ww => by rw [hI2]; simp only [rewAct]; cases a <;> rfl) (cI1 b) (cI2 b) ip
  obtain ⟨T₂, h2, hm2⟩ := hrw
  refine ⟨k.toNat + 1 + T₂, by rw [rrun_add, h1, h2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t (k.toNat + 1) with h | h
  · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
    exact ⟨jRB b, ip, q, hq, cRB b, hq1, by omega⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = k.toNat + 1 + t' := ⟨t - (k.toNat + 1), by omega⟩
    rw [rrun_add, h1]
    obtain ⟨s', ip', hs', hc'⟩ := hm2 t' (by omega)
    exact ⟨s', ip', 0, hs', hc', by omega, by omega⟩

include hC cC in
/-- The comparison walk of the plain mode: the input word starting at input position `q₀`
runs to the end of the input.

**Proof sketch.** Induction on `u₁`. Equal letters on the input and the register move both heads
right, extending the common prefix. A mismatch, or one word ending before the other, branches to
`jRB false`; both ending together branches to `jRB true`. The register head stays within `[0,
|wr|]`. -/
lemma cmpPlain_run (c : Cfg m Bool Λ x) (wr wi : List Bool)
    (hw : c.workTapes r = FinTM.bufferTape wr) (q₀ : ℕ)
    (hin : ∀ k, inSym x (q₀ + k) = wi[k]?) (hq : q₀ + wi.length ≤ x.length + 1) :
    ∀ (u₁ u₂ pre : List Bool) (ip : Fin (x.length + 2)), wi = pre ++ u₁ → wr = pre ++ u₂ →
      ip.val = q₀ + pre.length →
      ∃ (T k : ℕ) (ipk : Fin (x.length + 2)), ipk.val = q₀ + k ∧ pre.length ≤ k ∧
        k ≤ wr.length ∧ k ≤ wi.length ∧
        rrun P oracle (xCfg c jC ip r pre.length) T =
          xCfg c (jRB (decide (wi = wr))) ipk r ((k : ℤ) - 1) ∧
        ∀ t < T, ∃ ip' q, rrun P oracle (xCfg c jC ip r pre.length) t = xCfg c jC ip' r q ∧
          0 ≤ q ∧ q ≤ wr.length := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ pre ip e1 e2 hip
    have ha : inSym x ip.val = none := by rw [hip, hin, e1]; simp
    cases u₂ with
    | nil =>
      have hc : c.workTapes r pre.length = none := by rw [hw, e2]; simp
      refine ⟨1, pre.length, ip, hip, le_rfl, by rw [e2]; simp, by rw [e1]; simp, ?_, ?_⟩
      · rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
        simp only [cmpAct, ↓reduceIte]
        rw [apply_xAct]
        have : decide (wi = wr) = true := by simp [e1, e2]
        rw [this]; simp [sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨ip, _, rfl, by omega, by rw [e2]; simp⟩
    | cons b u₂' =>
      have hc : c.workTapes r pre.length = some b := by rw [hw, e2]; simp
      refine ⟨1, pre.length, ip, hip, le_rfl, by rw [e2]; simp, by rw [e1]; simp, ?_, ?_⟩
      · rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
        simp only [cmpAct, reduceCtorEq, ↓reduceIte]
        rw [apply_xAct]
        have : decide (wi = wr) = false := by simp [e1, e2]
        rw [this]; simp [sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨ip, _, rfl, by omega, by rw [e2]; simp; omega⟩
  | cons a u₁' ih =>
    intro u₂ pre ip e1 e2 hip
    have ha : inSym x ip.val = some a := by rw [hip, hin, e1]; simp
    cases u₂ with
    | nil =>
      have hc : c.workTapes r pre.length = none := by rw [hw, e2]; simp
      refine ⟨1, pre.length, ip, hip, le_rfl, by rw [e2]; simp, by rw [e1]; simp, ?_, ?_⟩
      · rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
        simp only [cmpAct, reduceCtorEq, ↓reduceIte]
        rw [apply_xAct]
        have : decide (wi = wr) = false := by simp [e1, e2]
        rw [this]; simp [sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨ip, _, rfl, by omega, by rw [e2]; simp⟩
    | cons b u₂' =>
      have hc : c.workTapes r pre.length = some b := by rw [hw, e2]; simp
      by_cases hab : a = b
      · subst hab
        have hlen : q₀ + (pre.length + 1) ≤ x.length + 1 := by
          have := congrArg List.length e1; simp at this; omega
        have hstep : rrun P oracle (xCfg c jC ip r pre.length) 1 =
            xCfg c jC ⟨q₀ + (pre ++ [a]).length, by simp; omega⟩ r (pre ++ [a]).length := by
          rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
          simp only [cmpAct, reduceCtorEq, ↓reduceIte]
          rw [apply_xAct]
          congr 1
          · exact Fin.ext (by rw [moveInputPos_pos_val _ (by omega)]; simp; omega)
          · simp
        obtain ⟨T, k, ipk, hipk, hk1, hk2, hk3, hr, hm⟩ := ih u₂' (pre ++ [a])
          ⟨q₀ + (pre ++ [a]).length, by simp; omega⟩ (by rw [e1]; simp) (by rw [e2]; simp) rfl
        refine ⟨1 + T, k, ipk, hipk, by simp at hk1; omega, hk2, hk3,
          by rw [rrun_add, hstep, hr], fun t ht => ?_⟩
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨ip, _, rfl, by omega, by rw [e2]; simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          exact hm t' (by omega)
      · refine ⟨1, pre.length, ip, hip, le_rfl, by rw [e2]; simp, by rw [e1]; simp, ?_, ?_⟩
        · rw [rrun_one_x P oracle c jC ip r _ cC, hC, xCfg_read, hc, ha]
          have hab' : (some a : Option Bool) ≠ some b := by simpa using hab
          simp only [cmpAct, hab', ↓reduceIte]
          rw [apply_xAct]
          have : decide (wi = wr) = false := by
            simp [e1, e2]; intro h; exact absurd h hab
          rw [this]; simp [sub_eq_add_neg]
        · intro t ht
          obtain rfl : t = 0 := by omega
          exact ⟨ip, _, rfl, by omega, by rw [e2]; simp; omega⟩

include hK hK2 hC hRB hI1 hI2 cK cK2 cC cRB cI1 cI2 in
/-- **Comparing a register with the index of a plain input**: on the input `⟨1ⁿ, w⟩`, with
`Nat.bits a` on register `r` (head on cell `0`), the fragment reaches `yes` if `w = Nat.bits a`
and `no` otherwise, input head and register head back home, the register head in
`[-1, |Nat.bits a|]` throughout.

**Proof sketch.** Skip the prefix `1²ⁿ 0 1` on the input (`skipPrefix_run`), compare `w` with
the register in lockstep (`cmpPlain_run`), then walk the register head back to cell `0`
(`regBack_x`) and rewind the input head (`rewind_x`). The outcome label is `yes` or `no`
according to `w = bits a`. -/
lemma jeqPlain_run (c : Cfg m Bool Λ x) (n : ℕ) (w : List Bool)
    (hx : x = pairEncode (List.replicate n true) w) (a : ℕ)
    (hreg : c.workTapes r = FinTM.bufferTape (Nat.bits a)) :
    ∃ T, rrun P oracle (xCfg c jK ⟨1, by omega⟩ r 0) T =
        xCfg c (if w = Nat.bits a then yes else no) ⟨1, by omega⟩ r 0 ∧
      ∀ t < T, ∃ s ip q, rrun P oracle (xCfg c jK ⟨1, by omega⟩ r 0) t = xCfg c s ip r q ∧
        P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits a).length := by
  have hxlen : x.length = 2 * n + 2 + w.length := by
    rw [hx]; simp [pairEncode_eq_dbl, dbl_replicate]; omega
  have hxg : ∀ k, x[k]? = if k < 2 * n then some true else if k = 2 * n then some false
      else if k = 2 * n + 1 then some true else w[k - (2 * n + 2)]? := by
    intro k
    rw [hx, pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
    by_cases h1 : k < 2 * n
    · rw [List.getElem?_append_left (by simp; omega)]; simp [h1]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate]
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 * n + j := ⟨k - 2 * n, by omega⟩
      simp only [Nat.add_sub_cancel_left, h1, ↓reduceIte]
      rcases j with _ | _ | j
      · simp
      · simp
      · simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
        rw [if_neg (by omega), if_neg (by omega)]
        congr 1; omega
  -- the run of `1`s
  have hscan := scanR P oracle c r 0 (fun _ => jK) 1 (2 * n) (by omega) (fun j hj ww => by
      rw [show 1 + j = j + 1 by ring, inSym_succ, hxg, if_pos hj, hK]; rfl)
    (fun j hj => cK)
  have h1 := hscan (2 * n) le_rfl
  have hs1 : rrun P oracle (xCfg c jK ⟨1 + 2 * n, by omega⟩ r 0) 1 =
      xCfg c jK2 ⟨2 + 2 * n, by omega⟩ r 0 := by
    rw [rrun_one_x P oracle c jK _ r 0 cK, hK]
    rw [show (⟨1 + 2 * n, _⟩ : Fin (x.length + 2)).val = 2 * n + 1 from by simp; ring, inSym_succ,
      hxg, if_neg (by omega), if_pos rfl]
    simp only [skipAct]
    rw [apply_xAct]
    congr 1
    exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
  have hs2 : rrun P oracle (xCfg c jK2 ⟨2 + 2 * n, by omega⟩ r 0) 1 =
      xCfg c jC ⟨3 + 2 * n, by omega⟩ r 0 := by
    rw [rrun_one_x P oracle c jK2 _ r 0 cK2, hK2, apply_xAct]
    congr 1
    exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; simp; omega)
  have hin : ∀ k, inSym x (3 + 2 * n + k) = w[k]? := by
    intro k
    rw [show 3 + 2 * n + k = (2 * n + 2 + k) + 1 by ring, inSym_succ, hxg,
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1; omega
  obtain ⟨T₃, k, ipk, hipk, -, hk2, hk3, h3, hm3⟩ := cmpPlain_run P oracle r jC jRB hC cC c
    (Nat.bits a) w hreg (3 + 2 * n) hin (by omega) w (Nat.bits a) [] ⟨3 + 2 * n, by omega⟩
    rfl rfl (by simp)
  obtain ⟨T₄, h4, hm4⟩ := cmpReturn P oracle r jRB jI1 jI2 yes no hRB hI1 hI2 cRB cI1 cI2 c
    (Nat.bits a) hreg (decide (w = Nat.bits a)) ipk k (by omega) (by omega)
  have hend : (if decide (w = Nat.bits a) = true then yes else no) =
      (if w = Nat.bits a then yes else no) := by simp
  rw [hend] at h4
  have hrun : rrun P oracle (xCfg c jK ⟨1, by omega⟩ r 0) (2 * n + 1 + 1) =
      xCfg c jC ⟨3 + 2 * n, by omega⟩ r 0 := by
    rw [rrun_add, rrun_add, h1, hs1, hs2]
  refine ⟨2 * n + 1 + 1 + T₃ + T₄, ?_, fun t ht => ?_⟩
  · simp only [List.length_nil, Nat.cast_zero] at h3
    rw [rrun_add, rrun_add, hrun, h3, h4]
  · simp only [List.length_nil, Nat.cast_zero] at h3 hm3
    rcases Nat.lt_or_ge t (2 * n + 1 + 1) with h | h
    · rcases Nat.lt_or_ge t (2 * n) with h' | h'
      · rw [hscan t h'.le]
        exact ⟨jK, _, 0, rfl, cK, by omega, by omega⟩
      · rcases Nat.lt_or_ge t (2 * n + 1) with h'' | h''
        · obtain rfl : t = 2 * n := by omega
          exact ⟨jK, _, 0, by rw [h1], cK, by omega, by omega⟩
        · obtain rfl : t = 2 * n + 1 := by omega
          exact ⟨jK2, _, 0, by rw [rrun_add, h1, hs1], cK2, by omega, by omega⟩
    · rcases Nat.lt_or_ge t (2 * n + 1 + 1 + T₃) with h' | h'
      · obtain ⟨t', rfl⟩ : ∃ t', t = 2 * n + 1 + 1 + t' := ⟨t - (2 * n + 2), by omega⟩
        rw [rrun_add, hrun]
        obtain ⟨ip', q, hq, hq1, hq2⟩ := hm3 t' (by omega)
        exact ⟨jC, ip', q, hq, cC, by omega, hq2⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 2 * n + 1 + 1 + T₃ + t' :=
          ⟨t - (2 * n + 2 + T₃), by omega⟩
        rw [rrun_add, rrun_add, hrun, h3]
        obtain ⟨s', ip', q, hq, hs', hq1, hq2⟩ := hm4 t' (by omega)
        exact ⟨s', ip', q, hq, hs', hq1, hq2⟩

end JeqPlain

end Complexity.LogProg
