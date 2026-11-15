/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Parse2

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Comparisons on inputs `⟨1ⁿ, ⟨u, w⟩⟩`

Program fragments comparing a register with the components of an input `⟨1ⁿ, ⟨u, w⟩⟩`:
with `w` (`Complexity.LogProg.jeqPairSnd_run`, after skipping the doubled `u`) and with `u`
(`Complexity.LogProg.jeqPairFst_run`, reading `u` doubled), in lockstep and without copying.

## Main definitions

* `Complexity.LogProg.ReachesB` — runs ending in one of two configurations.

## Main results

* `Complexity.LogProg.jeqPairSnd_run`, `Complexity.LogProg.jeqPairFst_run` — the comparisons.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-! ## Comparisons on pair inputs -/

/-- First symbol of a skipped pair. -/
def pskip1Act (r : Fin m) (jP2F jP2T : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 jP2T
  | _ => xAct r 1 0 jP2F

/-- Second symbol of a skipped pair: `01` ends the pairs. -/
def pskip2Act (r : Fin m) (jP1 jC : Λ) (b₁ : Bool) (a : Option Bool) : Action m Bool Λ :=
  if b₁ = false ∧ a = some true then xAct r 1 0 jC else xAct r 1 0 jP1

/-- The input symbols of `⟨1ⁿ, ⟨u, w⟩⟩` after the end marker spell `1²ⁿ 01 dbl u 01 w`. -/
lemma inSym_pairInput (n : ℕ) (u w : List Bool) (k : ℕ) :
    inSym (pairEncode (List.replicate n true) (pairEncode u w)) (k + 1) =
      (List.replicate (2 * n) true ++ [false, true] ++ dbl u ++ [false, true] ++ w)[k]? := by
  rw [inSym_succ]; simp [pairEncode_eq_dbl, dbl_replicate]

section PairSkip

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (jP1 jP2F jP2T jC : Λ)
  (hP1 : ∀ a w, P.tm.tr jP1 a w = pskip1Act r jP2F jP2T a)
  (hP2F : ∀ a w, P.tm.tr jP2F a w = pskip2Act r jP1 jC false a)
  (hP2T : ∀ a w, P.tm.tr jP2T a w = pskip2Act r jP1 jC true a)
  (cP1 : P.call jP1 = none) (cP2F : P.call jP2F = none) (cP2T : P.call jP2T = none)

include hP1 hP2F hP2T cP1 cP2F cP2T in
/-- Skipping the doubled word and its separator.

**Proof sketch.** Induction on `u`: each doubled letter `b b` is skipped in two steps
(`pskip1Act`, `pskip2Act`), and the separator `0 1` moves to `jC`. The input head ends just
after the separator; the register head never moves. -/
lemma pairSkip_run (c : Cfg m Bool Λ x) (p : ℤ) :
    ∀ (u : List Bool) (q : ℕ) (hq : q + 2 * u.length + 2 ≤ x.length + 1),
      (∀ k < 2 * u.length + 2, inSym x (q + k) = (dbl u ++ [false, true])[k]?) →
      Reaches P oracle (xCfg c jP1 ⟨q, by omega⟩ r p)
        (xCfg c jC ⟨q + 2 * u.length + 2, by omega⟩ r p) c r p := by
  intro u
  induction u with
  | nil =>
    intro q hq hin
    have h0 : inSym x q = some false := by simpa using hin 0 (by simp)
    have h1 : inSym x (q + 1) = some true := by simpa using hin 1 (by simp)
    have s1 : rrun P oracle (xCfg c jP1 ⟨q, by omega⟩ r p) 1 = xCfg c jP2F ⟨q + 1, by simp at hq; omega⟩ r p :=
      reaches_right P oracle r _ _ q (by simp at hq; omega) cP1 (fun w => by rw [hP1, h0]; rfl)
    have s2 : rrun P oracle (xCfg c jP2F ⟨q + 1, by simp at hq; omega⟩ r p) 1 =
        xCfg c jC ⟨q + 1 + 1, by simp at hq; omega⟩ r p :=
      reaches_right P oracle r _ _ (q + 1) (by simp at hq; omega) cP2F
        (fun w => by rw [hP2F, h1]; simp [pskip2Act])
    refine Reaches.step P oracle r _ _ rfl cP1 s1 (Reaches.step P oracle r _ _ rfl cP2F s2 ?_)
    convert Reaches.refl P oracle r _ c p using 3
  | cons b u ih =>
    intro q hq hin
    simp only [List.length_cons] at hq
    have h0 : inSym x q = some b := by simpa using hin 0 (by simp)
    have h1 : inSym x (q + 1) = some b := by simpa using hin 1 (by simp)
    have s1 : rrun P oracle (xCfg c jP1 ⟨q, by omega⟩ r p) 1 =
        xCfg c (if b then jP2T else jP2F) ⟨q + 1, by omega⟩ r p :=
      reaches_right P oracle r _ _ q (by omega) cP1 (fun w => by rw [hP1, h0]; cases b <;> rfl)
    have s2 : rrun P oracle (xCfg c (if b then jP2T else jP2F) ⟨q + 1, by omega⟩ r p) 1 =
        xCfg c jP1 ⟨q + 1 + 1, by omega⟩ r p :=
      reaches_right P oracle r _ _ (q + 1) (by omega) (by cases b <;> assumption)
        (fun w => by cases b <;> simp [hP2T, hP2F, h1, pskip2Act])
    have hin' : ∀ k < 2 * u.length + 2, inSym x (q + 2 + k) = (dbl u ++ [false, true])[k]? := by
      intro k hk
      rw [show q + 2 + k = q + (k + 2) by ring, hin (k + 2) (by simp; omega)]
      simp
    have := ih (q + 2) (by omega) hin'
    refine Reaches.step P oracle r _ _ rfl cP1 s1
      (Reaches.step P oracle r _ _ rfl (by cases b <;> assumption) s2 ?_)
    convert this using 3
    try (simp; omega)

end PairSkip

/-- Compare a doubled input word with a register: the first copy. -/
def dcmp1Act (r : Fin m) (jD2F jD2T : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some true => xAct r 1 0 jD2T
  | _ => xAct r 1 0 jD2F

/-- Compare a doubled input word with a register: the second copy (or the separator). -/
def dcmp2Act (r : Fin m) (jD1 : Λ) (jRB : Bool → Λ) (b₁ : Bool) (a c : Option Bool) :
    Action m Bool Λ :=
  if b₁ = false ∧ a = some true then xAct r 0 (-1) (jRB (decide (c = none)))
  else if c = some b₁ then xAct r 1 1 jD1 else xAct r 0 (-1) (jRB false)

section DblCmp

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (jD1 jD2F jD2T : Λ) (jRB : Bool → Λ)
  (hD1 : ∀ a w, P.tm.tr jD1 a w = dcmp1Act r jD2F jD2T a)
  (hD2F : ∀ a w, P.tm.tr jD2F a w = dcmp2Act r jD1 jRB false a (w r))
  (hD2T : ∀ a w, P.tm.tr jD2T a w = dcmp2Act r jD1 jRB true a (w r))
  (cD1 : P.call jD1 = none) (cD2F : P.call jD2F = none) (cD2T : P.call jD2T = none)

include hD1 hD2F hD2T cD1 cD2F cD2T in
/-- The comparison walk of the doubled mode.

**Proof sketch.** Induction on `u₁`. A doubled input letter `b b` equal to the register letter
moves the input head two cells and the register head one cell. A mismatch, or reaching the
separator `0 1` before or after the register word ends, branches to `jRB false`; reaching both
ends together branches to `jRB true`. -/
lemma cmpDbl_run (c : Cfg m Bool Λ x) (wr : List Bool) (hw : c.workTapes r = FinTM.bufferTape wr)
    (wi : List Bool) (q₀ : ℕ) (hq : q₀ + 2 * wi.length + 2 ≤ x.length + 1)
    (hin : ∀ k < 2 * wi.length + 2, inSym x (q₀ + k) = (dbl wi ++ [false, true])[k]?) :
    ∀ (u₁ u₂ pre : List Bool) (ip : Fin (x.length + 2)), wi = pre ++ u₁ → wr = pre ++ u₂ →
      ip.val = q₀ + 2 * pre.length →
      ∃ (T k : ℕ) (ipk : Fin (x.length + 2)), pre.length ≤ k ∧ k ≤ wr.length ∧
        rrun P oracle (xCfg c jD1 ip r pre.length) T =
          xCfg c (jRB (decide (wi = wr))) ipk r ((k : ℤ) - 1) ∧
        ∀ t < T, ∃ s ip' q, rrun P oracle (xCfg c jD1 ip r pre.length) t = xCfg c s ip' r q ∧
          P.call s = none ∧ 0 ≤ q ∧ q ≤ wr.length := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ pre ip e1 e2 hip
    subst e1
    have h0 : inSym x ip.val = some false := by
      rw [hip, show q₀ + 2 * pre.length = q₀ + 2 * (pre ++ []).length by simp]
      rw [hin _ (by simp)]; simp
    have h1 : inSym x (ip.val + 1) = some true := by
      rw [hip, show q₀ + 2 * pre.length + 1 = q₀ + (2 * (pre ++ []).length + 1) by simp; ring]
      rw [hin _ (by simp)]; simp
    have s1 : rrun P oracle (xCfg c jD1 ip r pre.length) 1 =
        xCfg c jD2F ⟨ip.val + 1, by simp at hq; omega⟩ r pre.length := by
      have := reaches_right P oracle (c := c) (p := (pre.length : ℤ)) r jD1 jD2F ip.val
        (by simp at hq; omega) cD1 (fun w => by rw [hD1, h0]; rfl)
      simpa using this
    have hcr : c.workTapes r pre.length = u₂.head? := by rw [hw, e2]; cases u₂ <;> simp
    have s2 : rrun P oracle (xCfg c jD2F ⟨ip.val + 1, by simp at hq; omega⟩ r pre.length) 1 =
        xCfg c (jRB (decide (pre ++ [] = wr))) ⟨ip.val + 1, by simp at hq; omega⟩ r
          ((pre.length : ℤ) - 1) := by
      rw [rrun_one_x P oracle c _ _ r _ cD2F, hD2F, xCfg_read, hcr]
      simp only
      rw [h1]
      simp only [dcmp2Act, and_self, ↓reduceIte]
      rw [apply_xAct]
      have : decide (u₂.head? = none) = decide (pre ++ [] = wr) := by
        rw [e2]; cases u₂ <;> simp
      rw [this]; simp [sub_eq_add_neg]
    refine ⟨1 + 1, pre.length, _, le_rfl, by rw [e2]; simp, by rw [rrun_add, s1, s2], ?_⟩
    intro t ht
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨jD1, ip, _, rfl, cD1, by omega, by rw [e2]; simp⟩
    · obtain rfl : t = 1 := by omega
      exact ⟨jD2F, _, _, s1, cD2F, by omega, by rw [e2]; simp⟩
  | cons b u₁' ih =>
    intro u₂ pre ip e1 e2 hip
    have hlen1 : wi.length = pre.length + 1 + u₁'.length := by rw [e1]; simp; ring
    have h0 : inSym x ip.val = some b := by
      rw [hip, hin _ (by omega), e1]
      rw [List.getElem?_append_left (by simp)]
      simp only [dbl]
      rw [List.flatMap_append, List.getElem?_append_right (by simp; omega)]
      simp [show 2 * pre.length - pre.length * 2 = 0 by omega]
    have h1 : inSym x (ip.val + 1) = some b := by
      rw [hip, show q₀ + 2 * pre.length + 1 = q₀ + (2 * pre.length + 1) by ring,
        hin _ (by omega), e1]
      rw [List.getElem?_append_left (by simp; omega)]
      simp only [dbl]
      rw [List.flatMap_append, List.getElem?_append_right (by simp; omega)]
      simp [show 2 * pre.length + 1 - pre.length * 2 = 1 by omega]
    have s1 : rrun P oracle (xCfg c jD1 ip r pre.length) 1 =
        xCfg c (if b then jD2T else jD2F) ⟨ip.val + 1, by omega⟩ r pre.length := by
      have := reaches_right P oracle (c := c) (p := (pre.length : ℤ)) r jD1
        (if b then jD2T else jD2F) ip.val (by omega) cD1
        (fun w => by rw [hD1, h0]; cases b <;> rfl)
      simpa using this
    have cb : P.call (if b then jD2T else jD2F) = none := by cases b <;> assumption
    have htr2 : ∀ a w, P.tm.tr (if b then jD2T else jD2F) a w = dcmp2Act r jD1 jRB b a (w r) := by
      intro a w; cases b
      · exact hD2F a w
      · exact hD2T a w
    by_cases hc : u₂.head? = some b
    · obtain ⟨u₂', rfl⟩ : ∃ u₂', u₂ = b :: u₂' := by
        cases u₂ with
        | nil => simp at hc
        | cons b' u₂' => simp at hc; exact ⟨u₂', by rw [hc]⟩
      have hcr : c.workTapes r pre.length = some b := by rw [hw, e2]; simp
      have s2 : rrun P oracle (xCfg c (if b then jD2T else jD2F) ⟨ip.val + 1, by omega⟩ r
          pre.length) 1 = xCfg c jD1 ⟨ip.val + 1 + 1, by omega⟩ r (pre ++ [b]).length := by
        rw [rrun_one_x P oracle c _ _ r _ cb, htr2, xCfg_read, hcr]
        simp only
        rw [h1]
        simp only [dcmp2Act]
        rw [if_neg (by cases b <;> simp)]
        simp only [↓reduceIte]
        rw [apply_xAct]
        congr 1
        · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)]; try simp)
        · simp
      obtain ⟨T, k, ipk, hk1, hk2, hr, hm⟩ := ih u₂' (pre ++ [b]) ⟨ip.val + 1 + 1, by omega⟩
        (by rw [e1]; simp) (by rw [e2]; simp) (by simp; omega)
      refine ⟨1 + 1 + T, k, ipk, by simp at hk1; omega, hk2, by rw [rrun_add, rrun_add, s1, s2, hr],
        fun t ht => ?_⟩
      rcases Nat.lt_or_ge t (1 + 1) with h | h
      · rcases Nat.lt_or_ge t 1 with h' | h'
        · obtain rfl : t = 0 := by omega
          exact ⟨jD1, ip, _, rfl, cD1, by omega, by rw [e2]; simp; omega⟩
        · obtain rfl : t = 1 := by omega
          exact ⟨_, _, _, s1, cb, by omega, by rw [e2]; simp; omega⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + 1 + t' := ⟨t - 2, by omega⟩
        rw [rrun_add, rrun_add, s1, s2]
        exact hm t' (by omega)
    · have hcr : c.workTapes r pre.length = u₂.head? := by rw [hw, e2]; cases u₂ <;> simp
      have hne : decide (wi = wr) = false := by
        rw [e1, e2]; simp; intro h; rw [← h] at hc; simp at hc
      have s2 : rrun P oracle (xCfg c (if b then jD2T else jD2F) ⟨ip.val + 1, by omega⟩ r
          pre.length) 1 = xCfg c (jRB (decide (wi = wr))) ⟨ip.val + 1, by omega⟩ r
            ((pre.length : ℤ) - 1) := by
        rw [rrun_one_x P oracle c _ _ r _ cb, htr2, xCfg_read, hcr]
        simp only
        rw [h1]
        simp only [dcmp2Act]
        rw [if_neg (by cases b <;> simp), if_neg hc, apply_xAct, hne]
        simp [sub_eq_add_neg]
      refine ⟨1 + 1, pre.length, _, le_rfl, by rw [e2]; simp, by rw [rrun_add, s1, s2], ?_⟩
      intro t ht
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨jD1, ip, _, rfl, cD1, by omega, by rw [e2]; simp⟩
      · obtain rfl : t = 1 := by omega
        exact ⟨_, _, _, s1, cb, by omega, by rw [e2]; simp⟩

end DblCmp

/-- Skipping the prefix `1²ⁿ 0 1`.

**Proof sketch.** The input head walks right over the `2n` leading `1`s with the state `jK`,
then over the `0` into `jK2`, which steps over the `1` into `nx` (`reaches_right` then two
single steps). The register head never moves. -/
lemma skipPrefix_run (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
    (jK jK2 nx : Λ) (hK : ∀ a w, P.tm.tr jK a w = skipAct r jK jK2 a)
    (hK2 : ∀ a w, P.tm.tr jK2 a w = xAct r 1 0 nx) (cK : P.call jK = none)
    (cK2 : P.call jK2 = none) (c : Cfg m Bool Λ x) (p : ℤ) (n : ℕ) (rest : List Bool)
    (hx : x = List.replicate (2 * n) true ++ [false, true] ++ rest) :
    Reaches P oracle (xCfg c jK ⟨1, by omega⟩ r p)
      (xCfg c nx ⟨3 + 2 * n, by rw [hx]; simp; omega⟩ r p) c r p := by
  have hxl : x.length = 2 * n + 2 + rest.length := by rw [hx]; simp; ring
  have hscan := scanR P oracle c r p (fun _ => jK) 1 (2 * n) (by omega) (fun j hj ww => by
      rw [show 1 + j = j + 1 by ring, inSym_succ, hx, List.append_assoc,
        List.getElem?_append_left (by simp; omega)]
      simp [hj, hK, skipAct])
    (fun j hj => cK)
  have h1 : inSym x (1 + 2 * n) = some false := by
    rw [show 1 + 2 * n = 2 * n + 1 by ring, inSym_succ, hx, List.append_assoc,
      List.getElem?_append_right (by simp)]; simp
  have s1 : rrun P oracle (xCfg c jK ⟨1 + 2 * n, by omega⟩ r p) 1 =
      xCfg c jK2 ⟨1 + 2 * n + 1, by omega⟩ r p :=
    reaches_right P oracle r _ _ (1 + 2 * n) (by omega) cK (fun w => by rw [hK, h1]; rfl)
  have s2 : rrun P oracle (xCfg c jK2 ⟨1 + 2 * n + 1, by omega⟩ r p) 1 =
      xCfg c nx ⟨1 + 2 * n + 1 + 1, by omega⟩ r p :=
    reaches_right P oracle r _ _ (1 + 2 * n + 1) (by omega) cK2 (fun w => hK2 _ w)
  have hr : Reaches P oracle (xCfg c jK ⟨1, by omega⟩ r p) (xCfg c jK ⟨1 + 2 * n, by omega⟩ r p)
      c r p := ⟨2 * n, hscan (2 * n) le_rfl, fun j hj => ⟨jK, _, hscan j hj.le, cK⟩⟩
  have := Reaches.trans P oracle r hr (Reaches.step P oracle r _ _ rfl cK s1
    (Reaches.step P oracle r _ _ rfl cK2 s2 (Reaches.refl P oracle r _ c p)))
  convert this using 3
  omega

/-- A run reaching a configuration with the head of register `r` in `[-1, L]` at every
step **strictly before the endpoint**: the reached configuration itself is not bounded by
this relation (`T = 0` gives a reflexive instance with the head anywhere). Consumers
needing the inclusive bound must add a separate endpoint hypothesis
(`-1 ≤ c₁.workTapePos r ∧ c₁.workTapePos r ≤ L`); note that `Reaches.toB` does
NOT supply it — it only converts a fixed pre-final coordinate bound into this
pre-final interval bound (P0 round 1 finding 6; round 2, residual). -/
def ReachesB (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c₀ c₁ c : Cfg m Bool Λ x)
    (r : Fin m) (L : ℤ) : Prop :=
  ∃ T, rrun P oracle c₀ T = c₁ ∧
    ∀ t < T, ∃ s ip q, rrun P oracle c₀ t = xCfg c s ip r q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ L

/-- A run whose pre-final steps all keep the register head at the fixed coordinate
`p ∈ [-1, L]` is a run whose pre-final steps keep it within `[-1, L]` — no bound on the
*reached* configuration's head is given or implied (P0 round 2, finding 6). -/
lemma Reaches.toB {P : RProg m d Λ} {oracle : Fin d → List Bool → Bool} {c₀ c₁ c : Cfg m Bool Λ x}
    {r : Fin m} {p L : ℤ} (h : Reaches P oracle c₀ c₁ c r p) (hp : -1 ≤ p ∧ p ≤ L) :
    ReachesB P oracle c₀ c₁ c r L := by
  obtain ⟨T, hT, hm⟩ := h
  exact ⟨T, hT, fun t ht => by obtain ⟨s, ip, h1, h2⟩ := hm t ht; exact ⟨s, ip, p, h1, h2, hp⟩⟩

/-- Runs with register heads within `[-1, L]` compose. -/
lemma ReachesB.trans {P : RProg m d Λ} {oracle : Fin d → List Bool → Bool}
    {c₀ c₁ c₂ c : Cfg m Bool Λ x} {r : Fin m} {L : ℤ} (h₁ : ReachesB P oracle c₀ c₁ c r L)
    (h₂ : ReachesB P oracle c₁ c₂ c r L) : ReachesB P oracle c₀ c₂ c r L := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- Indexing `pre ++ rest` past `pre` indexes `rest`. -/
lemma getElem?_append_len (pre rest : List Bool) (k : ℕ) :
    (pre ++ rest)[pre.length + k]? = rest[k]? := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

section JeqPair

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (jK jK2 jC : Λ) (jRB jI1 jI2 : Bool → Λ) (yes no : Λ)
  (hK : ∀ a w, P.tm.tr jK a w = skipAct r jK jK2 a)
  (hC : ∀ a w, P.tm.tr jC a w = cmpAct r jC jRB a (w r))
  (hRB : ∀ b a w, P.tm.tr (jRB b) a w = backAct r (jRB b) (jI1 b) (w r))
  (hI1 : ∀ b a w, P.tm.tr (jI1 b) a w = xAct r (-1) 0 (jI2 b))
  (hI2 : ∀ b a w, P.tm.tr (jI2 b) a w = rewAct r (jI2 b) (if b then yes else no) a)
  (cK : P.call jK = none) (cK2 : P.call jK2 = none) (cC : P.call jC = none)
  (cRB : ∀ b, P.call (jRB b) = none) (cI1 : ∀ b, P.call (jI1 b) = none)
  (cI2 : ∀ b, P.call (jI2 b) = none)

include hK hC hRB hI1 hI2 cK cK2 cC cRB cI1 cI2 in
/-- **Comparing a register with the second index of a pair input** `⟨1ⁿ, ⟨u, w⟩⟩`: reach `yes`
if `w = Nat.bits a`, `no` otherwise.

**Proof sketch.** Skip the prefix `1²ⁿ 0 1` (`skipPrefix_run`) and the doubled `u` with its
separator (`pairSkip_run`). Then compare `w` with the register (`cmpPlain_run`), walk the
register head back (`regBack_x`) and rewind the input head (`rewind_x`). -/
lemma jeqPairSnd_run (jP1 jP2F jP2T : Λ)
    (hK2 : ∀ a w, P.tm.tr jK2 a w = xAct r 1 0 jP1)
    (hP1 : ∀ a w, P.tm.tr jP1 a w = pskip1Act r jP2F jP2T a)
    (hP2F : ∀ a w, P.tm.tr jP2F a w = pskip2Act r jP1 jC false a)
    (hP2T : ∀ a w, P.tm.tr jP2T a w = pskip2Act r jP1 jC true a)
    (cP1 : P.call jP1 = none) (cP2F : P.call jP2F = none) (cP2T : P.call jP2T = none)
    (c : Cfg m Bool Λ x) (n : ℕ) (u w : List Bool)
    (hx : x = pairEncode (List.replicate n true) (pairEncode u w)) (a : ℕ)
    (hreg : c.workTapes r = FinTM.bufferTape (Nat.bits a)) :
    ReachesB P oracle (xCfg c jK ⟨1, by omega⟩ r 0)
      (xCfg c (if w = Nat.bits a then yes else no) ⟨1, by omega⟩ r 0) c r (Nat.bits a).length := by
  have hx' : x = List.replicate (2 * n) true ++ [false, true] ++ (dbl u ++ [false, true] ++ w) := by
    rw [hx]; simp [pairEncode_eq_dbl, dbl_replicate]
  have hxl : x.length = 2 * n + 2 + (2 * u.length + 2 + w.length) := by rw [hx']; simp; ring
  have h1 := skipPrefix_run P oracle r jK jK2 jP1 hK hK2 cK cK2 c 0 n _ hx'
  have h2 := pairSkip_run P oracle r jP1 jP2F jP2T jC hP1 hP2F hP2T cP1 cP2F cP2T c 0 u (3 + 2 * n)
    (by omega) (fun k hk => by
      have e : 3 + 2 * n + k = (List.replicate (2 * n) true ++ [false, true]).length + k + 1 := by
        simp; ring
      rw [e, inSym_succ, hx', getElem?_append_len, List.getElem?_append_left (by simp; omega)])
  have hin : ∀ k, inSym x (3 + 2 * n + 2 * u.length + 2 + k) = w[k]? := by
    intro k
    have e : 3 + 2 * n + 2 * u.length + 2 + k = (List.replicate (2 * n) true ++
        [false, true]).length + ((dbl u ++ [false, true]).length + k) + 1 := by simp; ring
    rw [e, inSym_succ, hx', getElem?_append_len, getElem?_append_len]
  obtain ⟨T₃, k, ipk, hipk, -, hk2, hk3, h3, hm3⟩ := cmpPlain_run P oracle r jC jRB hC cC c
    (Nat.bits a) w hreg (3 + 2 * n + 2 * u.length + 2) hin (by omega) w (Nat.bits a) []
    ⟨3 + 2 * n + 2 * u.length + 2, by omega⟩ rfl rfl (by simp)
  obtain ⟨T₄, h4, hm4⟩ := cmpReturn P oracle r jRB jI1 jI2 yes no hRB hI1 hI2 cRB cI1 cI2 c
    (Nat.bits a) hreg (decide (w = Nat.bits a)) ipk k (by omega) (by omega)
  simp only [List.length_nil, Nat.cast_zero, decide_eq_true_eq] at h3 hm3 h4
  have hb : ((-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ (Nat.bits a).length) := ⟨by omega, by omega⟩
  refine ((h1.toB hb).trans (h2.toB hb)).trans ?_
  refine ⟨T₃ + T₄, by rw [rrun_add, h3, h4], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₃ with h | h
  · obtain ⟨ip', q, hq, hq1, hq2⟩ := hm3 t h
    exact ⟨jC, ip', q, hq, cC, by omega, hq2⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₃ + t' := ⟨t - T₃, by omega⟩
    rw [rrun_add, h3]
    exact hm4 t' (by omega)

include hK hRB hI1 hI2 cK cK2 cRB cI1 cI2 in
/-- **Comparing a register with the first index of a pair input** `⟨1ⁿ, ⟨u, w⟩⟩`: reach
`yes` if `u = Nat.bits a`, `no` otherwise.

**Proof sketch.** Skip the prefix `1²ⁿ 0 1` (`skipPrefix_run`). Then compare the doubled `u`
with the register (`cmpDbl_run`), walk the register head back (`regBack_x`) and rewind the input
head (`rewind_x`). -/
lemma jeqPairFst_run (jD1 jD2F jD2T : Λ)
    (hK2 : ∀ a w, P.tm.tr jK2 a w = xAct r 1 0 jD1)
    (hD1 : ∀ a w, P.tm.tr jD1 a w = dcmp1Act r jD2F jD2T a)
    (hD2F : ∀ a w, P.tm.tr jD2F a w = dcmp2Act r jD1 jRB false a (w r))
    (hD2T : ∀ a w, P.tm.tr jD2T a w = dcmp2Act r jD1 jRB true a (w r))
    (cD1 : P.call jD1 = none) (cD2F : P.call jD2F = none) (cD2T : P.call jD2T = none)
    (c : Cfg m Bool Λ x) (n : ℕ) (u w : List Bool)
    (hx : x = pairEncode (List.replicate n true) (pairEncode u w)) (a : ℕ)
    (hreg : c.workTapes r = FinTM.bufferTape (Nat.bits a)) :
    ReachesB P oracle (xCfg c jK ⟨1, by omega⟩ r 0)
      (xCfg c (if u = Nat.bits a then yes else no) ⟨1, by omega⟩ r 0) c r (Nat.bits a).length := by
  have hx' : x = List.replicate (2 * n) true ++ [false, true] ++ (dbl u ++ [false, true] ++ w) := by
    rw [hx]; simp [pairEncode_eq_dbl, dbl_replicate]
  have hxl : x.length = 2 * n + 2 + (2 * u.length + 2 + w.length) := by rw [hx']; simp; ring
  have h1 := skipPrefix_run P oracle r jK jK2 jD1 hK hK2 cK cK2 c 0 n _ hx'
  obtain ⟨T₂, k, ipk, -, hk2, h2, hm2⟩ := cmpDbl_run P oracle r jD1 jD2F jD2T jRB hD1 hD2F hD2T
    cD1 cD2F cD2T c (Nat.bits a) hreg u (3 + 2 * n) (by omega) (fun k hk => by
      have e : 3 + 2 * n + k = (List.replicate (2 * n) true ++ [false, true]).length + k + 1 := by
        simp; ring
      rw [e, inSym_succ, hx', getElem?_append_len, List.getElem?_append_left (by simp; omega)])
    u (Nat.bits a) [] ⟨3 + 2 * n, by omega⟩ rfl rfl (by simp)
  have hk0 : (0 : ℤ) ≤ k := by omega
  obtain ⟨T₄, h4, hm4⟩ := cmpReturn P oracle r jRB jI1 jI2 yes no hRB hI1 hI2 cRB cI1 cI2 c
    (Nat.bits a) hreg (decide (u = Nat.bits a)) ipk k hk0 (by omega)
  simp only [List.length_nil, Nat.cast_zero, decide_eq_true_eq] at h2 hm2 h4
  have hb : ((-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ (Nat.bits a).length) := ⟨by omega, by omega⟩
  refine (h1.toB hb).trans ?_
  refine ⟨T₂ + T₄, by rw [rrun_add, h2, h4], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₂ with h | h
  · obtain ⟨s', ip', q, hq, hs', hq1, hq2⟩ := hm2 t h
    exact ⟨s', ip', q, hq, hs', by omega, hq2⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₂ + t' := ⟨t - T₂, by omega⟩
    rw [rrun_add, h2]
    exact hm4 t' (by omega)

end JeqPair

end Complexity.LogProg
