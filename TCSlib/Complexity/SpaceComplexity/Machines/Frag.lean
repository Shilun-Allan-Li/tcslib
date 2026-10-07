/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.FragDec

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: decrement, clear, halve

More single-register fragments of register-tape programs, in the style of
`Complexity.LogProg.inc_run`: each is specified by its transitions and proved once against
the program semantics. Counters are the words `Nat.bits n` from cell `0`.

The decrement and clear fragments are in
`TCSlib.Complexity.SpaceComplexity.Machines.FragDec`, which this file re-exports; this file
has the halving and equality fragments.

## Main definitions

* `Complexity.LogProg.decW` — the decrement of a little-endian word.

## Main results

* `Complexity.LogProg.dec_run` — `Nat.bits n ↦ Nat.bits (n - 1)`.
* `Complexity.LogProg.clr_run` — `Nat.bits n ↦ Nat.bits 0`.
* `Complexity.LogProg.half_run` — `Nat.bits n ↦ Nat.bits (n / 2)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## The halving fragment -/

/-- The left walk of the halving: write the carried symbol (the cell to the right), carry the
current one; at the left blank step onto cell `0` and continue. -/
def halfLAct {m : ℕ} {Λ : Type} (r : Fin m) (carry : Option Bool) (hF hT next : Λ)
    (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some b => regAct r (some carry) (-1) (if b then hT else hF)
  | none => regAct r none 1 next

section Half

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (hR h0 hF hT next : Λ)
  (hRt : ∀ a w, P.tm.tr hR a w = toEndAct r hR h0 (w r))
  (h0t : ∀ a w, P.tm.tr h0 a w = halfLAct r none hF hT next (w r))
  (hFt : ∀ a w, P.tm.tr hF a w = halfLAct r (some false) hF hT next (w r))
  (hTt : ∀ a w, P.tm.tr hT a w = halfLAct r (some true) hF hT next (w r))
  (hRc : P.call hR = none) (h0c : P.call h0 = none) (hFc : P.call hF = none)
  (hTc : P.call hT = none)

/-- The left-walk state carrying a given optional symbol. -/
def halfSt (h0 hF hT : Λ) : Option Bool → Λ
  | none => h0
  | some false => hF
  | some true => hT

include h0t hFt hTt h0c hFc hTc in
/-- **The shifting walk** of the halving fragment: from the position `k - 1` after the first `k`
letters have been shifted, carrying `w[k]` in the state, the program shifts the remaining
letters one cell left and returns to cell `0` with `w.tail` written.

**Proof sketch.** Induction on `k`. Each step writes the carried letter, picks up the letter
under the head and moves left. At the left blank the head moves right onto cell `0`, and the
tape holds `w` with its first letter dropped. -/
lemma halfL_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ k ≤ w.length,
      rrun P oracle (regCfg c (halfSt h0 hF hT w[k]?) r (FinTM.bufferTape (w.take k ++ w.drop (k + 1)))
          ((k : ℤ) - 1)) (k + 1) =
        regCfg c next r (FinTM.bufferTape w.tail) 0 ∧
      ∀ t < k + 1, ∃ s f q, rrun P oracle (regCfg c (halfSt h0 hF hT w[k]?) r
          (FinTM.bufferTape (w.take k ++ w.drop (k + 1))) ((k : ℤ) - 1)) t =
          regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (k : ℤ) - 1 := by
  have htr : ∀ (cr : Option Bool) a ww, P.tm.tr (halfSt h0 hF hT cr) a ww =
      halfLAct r cr hF hT next (ww r) := by
    intro cr a ww; rcases cr with _ | _ | _
    · exact h0t a ww
    · exact hFt a ww
    · exact hTt a ww
  have hc : ∀ cr, P.call (halfSt h0 hF hT cr) = none := by
    intro cr; rcases cr with _ | _ | _
    · exact h0c
    · exact hFc
    · exact hTc
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨_, _, _, rfl, hc _, by omega, le_rfl⟩
    rw [rrun_one_reg P oracle r c _ _ _ (hc _), htr, regCfg_read]
    have hrd : FinTM.bufferTape (w.take 0 ++ w.drop (0 + 1)) (((0 : ℕ) : ℤ) - 1) = none := by
      simp
    rw [hrd]
    simp only [halfLAct]
    rw [apply_regAct]
    simp [List.drop_one]
  | succ k ih =>
    intro hk
    have hkw : k < w.length := by omega
    have hlen : (w.take k).length = k := List.length_take_of_le (by omega)
    have hsplit : w.take (k + 1) ++ w.drop (k + 1 + 1) = w.take k ++ w[k] :: w.drop (k + 2) := by
      have h1 : w.take (k + 1) = w.take k ++ [w[k]] := by
        rw [List.take_succ, List.getElem?_eq_getElem hkw]; rfl
      rw [h1, List.append_assoc]; rfl
    have hstep : rrun P oracle (regCfg c (halfSt h0 hF hT w[k + 1]?) r
        (FinTM.bufferTape (w.take (k + 1) ++ w.drop (k + 1 + 1))) (((k + 1 : ℕ) : ℤ) - 1)) 1 =
        regCfg c (halfSt h0 hF hT w[k]?) r (FinTM.bufferTape (w.take k ++ w.drop (k + 1)))
          ((k : ℤ) - 1) := by
      rw [rrun_one_reg P oracle r c _ _ _ (hc _), htr, regCfg_read, hsplit]
      have hpos : (((k + 1 : ℕ) : ℤ) - 1) = ((w.take k).length : ℤ) := by
        rw [hlen]; push_cast; ring
      have hrd : FinTM.bufferTape (w.take k ++ w[k] :: w.drop (k + 2))
          (((k + 1 : ℕ) : ℤ) - 1) = some w[k] := by
        rw [hpos]; simp
      rw [hrd]
      simp only [halfLAct]
      rw [apply_regAct]
      dsimp only
      rw [List.getElem?_eq_getElem hkw]
      congr 1
      · cases w[k] <;> rfl
      · rw [hpos]
        rcases hk2 : w[k + 1]? with _ | v
        · -- `k + 1 = |w|`: erase the last cell
          have hkl : k + 1 = w.length := by
            by_contra hne; rw [List.getElem?_eq_getElem (by omega)] at hk2; simp at hk2
          have hd1 : w.drop (k + 2) = [] := List.drop_eq_nil_of_le (by omega)
          have hd2 : w.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
          rw [hd1, hd2, bufferTape_erase_last]; simp
        · have hd : w.drop (k + 1) = v :: w.drop (k + 2) := by
            rw [List.drop_eq_getElem_cons (by
              by_contra hne; rw [List.getElem?_eq_none (by omega)] at hk2; simp at hk2)]
            congr 1
            rw [List.getElem?_eq_getElem (by
              by_contra hne; rw [List.getElem?_eq_none (by omega)] at hk2; simp at hk2)] at hk2
            simpa using hk2
          rw [hd, update_bufferTape_cons]
      · simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [rrun_succ_left, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨_, _, _, rfl, hc _, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨s', f, q, hq, hs', h1, h2⟩ := ihm t' (by omega)
        exact ⟨s', f, q, hq, hs', h1, by push_cast at h2 ⊢; omega⟩

include hRt hRc h0t hFt hTt h0c hFc hTc in
/-- **The halving fragment**: `Nat.bits n ↦ Nat.bits (n / 2)` on register `r` (drop the
first binary digit), head back on cell `0`, head in `[-1, |Nat.bits n|]` throughout.

**Proof sketch.** Walk to the right end of `bits n` (`toEnd_run`), then shift every letter one
cell left while walking back (`halfL_run`), which drops the first letter. Since `bits (n / 2)`
is the tail of `bits n` (`bits_half`), the register holds `bits (n / 2)`. -/
lemma half_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c hR r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n / 2))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c hR r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  set w := Nat.bits n
  obtain ⟨h1, hm1⟩ := toEnd_run P oracle r hR h0 hRt hRc c w w.length 0 (by simp) le_rfl
  obtain ⟨h2, hm2⟩ := halfL_run P oracle r h0 hF hT next h0t hFt hTt h0c hFc hTc c w w.length
    le_rfl
  have he : w.take w.length ++ w.drop (w.length + 1) = w := by simp
  have hn : w[w.length]? = none := by simp
  rw [he, hn] at h2 hm2
  refine ⟨w.length + 1 + (w.length + 1), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1]
    convert h2 using 3
    · rw [bits_half]
  · rcases Nat.lt_or_ge t (w.length + 1) with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨hR, _, q, hq, hRc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = w.length + 1 + t' := ⟨t - (w.length + 1), by omega⟩
      rw [rrun_add, h1]
      obtain ⟨s', f, q, hq, hs', hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨s', f, q, hq, hs', hq1, by omega⟩

end Half

/-! ## The equality test of two registers -/

section Eq

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A configuration with state `s` and the heads of registers `r₁`, `r₂` at `k`. -/
def eqCfg (c : Cfg m Bool Λ x) (s : Λ) (r₁ r₂ : Fin m) (k : ℤ) : Cfg m Bool Λ x :=
  ⟨some s, c.inputPos, c.workTapes,
    Function.update (Function.update c.workTapePos r₁ k) r₂ k, c.output⟩

/-- Move the heads of `r₁` and `r₂` together. -/
def mv2Act (r₁ r₂ : Fin m) (mv : SignType) (s : Λ) : Action m Bool Λ :=
  ⟨0, fun r => if r = r₁ ∨ r = r₂ then (none, mv) else (none, 0), none, some s⟩

/-- Applying the two-register move action moves both register heads by `mv` and enters `s'`. -/
lemma apply_mv2Act (c : Cfg m Bool Λ x) (s s' : Λ) (r₁ r₂ : Fin m) (k : ℤ) (mv : SignType) :
    (mv2Act r₁ r₂ mv s').apply (eqCfg c s r₁ r₂ k) = eqCfg c s' r₁ r₂ (k + mv) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [mv2Act, eqCfg])
  · funext r z
    simp only [mv2Act, eqCfg, Action.apply]
    split_ifs <;> rfl
  · funext r
    simp only [mv2Act, eqCfg, Action.apply, Function.update_apply]
    by_cases h2 : r = r₂
    · simp [h2]
    · by_cases h1 : r = r₁
      · simp [h1]
      · simp [h1, h2]

/-- The comparison step. -/
def eqCAct (r₁ r₂ : Fin m) (eC eBy eBn : Λ) (a b : Option Bool) : Action m Bool Λ :=
  if a = b then (if a = none then mv2Act r₁ r₂ (-1) eBy else mv2Act r₁ r₂ 1 eC)
  else mv2Act r₁ r₂ (-1) eBn

/-- The return step (reading register `r₁`). -/
def eqBAct (r₁ r₂ : Fin m) (eB l : Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some _ => mv2Act r₁ r₂ (-1) eB
  | none => mv2Act r₁ r₂ 1 l

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r₁ r₂ : Fin m)
  (hne : r₁ ≠ r₂) (eC eBy eBn yes no : Λ)
  (hC : ∀ a w, P.tm.tr eC a w = eqCAct r₁ r₂ eC eBy eBn (w r₁) (w r₂))
  (hBy : ∀ a w, P.tm.tr eBy a w = eqBAct r₁ r₂ eBy yes (w r₁))
  (hBn : ∀ a w, P.tm.tr eBn a w = eqBAct r₁ r₂ eBn no (w r₁))
  (hCc : P.call eC = none) (hByc : P.call eBy = none) (hBnc : P.call eBn = none)

include hne in
/-- The two-register view reads register `r₁` at its head position `k`. -/
lemma eqCfg_read₁ (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) :
    (eqCfg c s r₁ r₂ k).workTapeSymbols r₁ = c.workTapes r₁ k := by
  simp [eqCfg, Cfg.workTapeSymbols, hne]

/-- The two-register view reads register `r₂` at its head position `k`. -/
lemma eqCfg_read₂ (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) :
    (eqCfg c s r₁ r₂ k).workTapeSymbols r₂ = c.workTapes r₂ k := by
  simp [eqCfg, Cfg.workTapeSymbols]

/-- One step of the program from a two-register view at a non-call state is the transition's
action applied to it. -/
lemma rrun_one_eq (c : Cfg m Bool Λ x) (s : Λ) (k : ℤ) (hs : P.call s = none) :
    rrun P oracle (eqCfg c s r₁ r₂ k) 1 =
      (P.tm.tr s (eqCfg c s r₁ r₂ k).inputSymbol (eqCfg c s r₁ r₂ k).workTapeSymbols).apply
        (eqCfg c s r₁ r₂ k) := by
  rw [rrun_one, rstep_noncall P oracle _ s rfl hs]
  unfold MultiTapeTM.step
  rfl

include hne hC hCc in
/-- **The comparison walk** of the equality test: from `eC` with both heads after the common prefix
`pre` of `w₁` and `w₂`, the program reaches `eBy` if `w₁ = w₂` and `eBn` otherwise, the heads
within `w₁`'s range.

**Proof sketch.** Induction on `u₁`. Equal letters move both heads right and extend the common
prefix. A mismatch, or one word ending before the other, enters `eBn`; both words ending
together enters `eBy`. -/
lemma eqC_run (c : Cfg m Bool Λ x) (w₁ w₂ : List Bool)
    (h₁ : c.workTapes r₁ = FinTM.bufferTape w₁) (h₂ : c.workTapes r₂ = FinTM.bufferTape w₂) :
    ∀ (u₁ u₂ pre : List Bool), w₁ = pre ++ u₁ → w₂ = pre ++ u₂ →
      ∃ (T : ℕ) (p : ℤ), (pre.length : ℤ) - 1 ≤ p ∧ p < w₁.length ∧
        rrun P oracle (eqCfg c eC r₁ r₂ pre.length) T =
          eqCfg c (if w₁ = w₂ then eBy else eBn) r₁ r₂ p ∧
        ∀ t < T, ∃ q, rrun P oracle (eqCfg c eC r₁ r₂ pre.length) t = eqCfg c eC r₁ r₂ q ∧
          (pre.length : ℤ) ≤ q ∧ q ≤ w₁.length := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ pre e1 e2
    refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp, ?_, ?_⟩
    · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁, h₂]
      have ha : FinTM.bufferTape w₁ pre.length = none := by rw [e1]; simp
      rw [ha]
      cases u₂ with
      | nil =>
        have hb : FinTM.bufferTape w₂ pre.length = none := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, ↓reduceIte]
        rw [apply_mv2Act]
        simp [e1, e2, sub_eq_add_neg]
      | cons b u₂' =>
        have hb : FinTM.bufferTape w₂ pre.length = some b := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, reduceCtorEq, ↓reduceIte]
        rw [apply_mv2Act]
        have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp
        simp [hneq, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, rfl, le_rfl, by rw [e1]; simp⟩
  | cons a u₁' ih =>
    intro u₂ pre e1 e2
    have ha : FinTM.bufferTape w₁ pre.length = some a := by rw [e1]; simp
    cases u₂ with
    | nil =>
      refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp; omega, ?_, ?_⟩
      · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁, h₂,
          ha]
        have hb : FinTM.bufferTape w₂ pre.length = none := by rw [e2]; simp
        rw [hb]
        simp only [eqCAct, reduceCtorEq, ↓reduceIte]
        rw [apply_mv2Act]
        have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp
        simp [hneq, sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩
    | cons b u₂' =>
      have hb : FinTM.bufferTape w₂ pre.length = some b := by rw [e2]; simp
      by_cases hab : a = b
      · subst hab
        obtain ⟨T, p, hp1, hp2, hr, hm⟩ := ih u₂' (pre ++ [a]) (by rw [e1]; simp)
          (by rw [e2]; simp)
        have hstep : rrun P oracle (eqCfg c eC r₁ r₂ pre.length) 1 =
            eqCfg c eC r₁ r₂ (pre ++ [a]).length := by
          rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁,
            h₂, ha, hb]
          simp only [eqCAct, reduceCtorEq, ↓reduceIte]
          rw [apply_mv2Act]
          simp
        refine ⟨1 + T, p, by simp at hp1; omega, hp2, by rw [rrun_add, hstep, hr], ?_⟩
        intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨q, hq, hq1, hq2⟩ := hm t' (by omega)
          exact ⟨q, hq, by simp at hq1; omega, hq2⟩
      · refine ⟨1, (pre.length : ℤ) - 1, le_rfl, by rw [e1]; simp; omega, ?_, ?_⟩
        · rw [rrun_one_eq P oracle r₁ r₂ c eC _ hCc, hC, eqCfg_read₁ r₁ r₂ hne, eqCfg_read₂, h₁,
            h₂, ha, hb]
          have hab' : (some a : Option Bool) ≠ some b := by simpa using hab
          simp only [eqCAct, hab', ↓reduceIte]
          rw [apply_mv2Act]
          have hneq : w₁ ≠ w₂ := by rw [e1, e2]; simp; intro h; exact absurd h hab
          simp [hneq, sub_eq_add_neg]
        · intro t ht
          obtain rfl : t = 0 := by omega
          exact ⟨_, rfl, le_rfl, by rw [e1]; simp; omega⟩

include hne in
/-- The return walk of the equality test (reading register `r₁`, whose cells left of the
start are nonblank).

**Proof sketch.** Induction on `n = p + 1`: on a letter of `w₁` both heads move left; at the
left blank both move right onto cell `0` and the state becomes `l`. The heads stay in `[-1, p]`. -/
lemma eqB_run (c : Cfg m Bool Λ x) (w₁ : List Bool) (h₁ : c.workTapes r₁ = FinTM.bufferTape w₁)
    (eB l : Λ) (hBt : ∀ a w, P.tm.tr eB a w = eqBAct r₁ r₂ eB l (w r₁))
    (hBc : P.call eB = none) :
    ∀ (n : ℕ) (p : ℤ), p + 1 = n → p < w₁.length →
      rrun P oracle (eqCfg c eB r₁ r₂ p) (n + 1) = eqCfg c l r₁ r₂ 0 ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (eqCfg c eB r₁ r₂ p) t = eqCfg c eB r₁ r₂ q ∧
        -1 ≤ q ∧ q ≤ p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    rw [rrun_one_eq P oracle r₁ r₂ c eB _ hBc, hBt, eqCfg_read₁ r₁ r₂ hne, h₁]
    have hrd : FinTM.bufferTape w₁ p = none := by rw [show p = -1 by omega]; simp
    rw [hrd]
    simp only [eqBAct]
    rw [apply_mv2Act]
    congr 1
  | succ n ih =>
    intro p hp hpw
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w₁.length := by omega
    have hstep : rrun P oracle (eqCfg c eB r₁ r₂ p) 1 = eqCfg c eB r₁ r₂ (p - 1) := by
      rw [rrun_one_eq P oracle r₁ r₂ c eB _ hBc, hBt, eqCfg_read₁ r₁ r₂ hne, h₁]
      have hrd : FinTM.bufferTape w₁ p = some w₁[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [eqBAct]
      rw [apply_mv2Act]
      simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (p - 1) (by omega) (by omega)
    refine ⟨by rw [rrun_succ_left, hstep, ihr], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
      rw [rrun_add, hstep]
      obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
      exact ⟨q, hq, h1, by omega⟩

include hne hC hBy hBn hCc hByc hBnc in
/-- **The equality test**: from `eC` with `Nat.bits a` on `r₁` and `Nat.bits b` on `r₂`, both
heads on cell `0`, the program reaches `yes` if `a = b` and `no` otherwise, heads back on
cell `0`, tapes unchanged; both heads stay in `[-1, |Nat.bits a|]`.

**Proof sketch.** Run the comparison walk (`eqC_run`) from the empty common prefix, reaching
`eBy` or `eBn` according to `bits a = bits b`, which is `a = b` by injectivity of `Nat.bits`.
Then run the return walk (`eqB_run`) back to cell `0`, ending in `yes` or `no`. -/
lemma eq_run (c : Cfg m Bool Λ x) (a b : ℕ)
    (h₁ : c.workTapes r₁ = FinTM.bufferTape (Nat.bits a))
    (h₂ : c.workTapes r₂ = FinTM.bufferTape (Nat.bits b)) :
    ∃ T, rrun P oracle (eqCfg c eC r₁ r₂ 0) T = eqCfg c (if a = b then yes else no) r₁ r₂ 0 ∧
      ∀ t < T, ∃ s q, rrun P oracle (eqCfg c eC r₁ r₂ 0) t = eqCfg c s r₁ r₂ q ∧
        P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits a).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := eqC_run P oracle r₁ r₂ hne eC eBy eBn hC hCc c _ _ h₁ h₂
    (Nat.bits a) (Nat.bits b) [] rfl rfl
  simp only [List.length_nil, Nat.cast_zero] at hp1 hr1 hm1
  have hiff : (Nat.bits a = Nat.bits b) ↔ a = b :=
    ⟨fun h => bits_injective h, fun h => by rw [h]⟩
  by_cases hab : a = b
  · have hw : Nat.bits a = Nat.bits b := hiff.mpr hab
    rw [if_pos hw] at hr1
    obtain ⟨hr2, hm2⟩ := eqB_run P oracle r₁ r₂ hne c _ h₁ eBy yes hBy hByc (p + 1).toNat p
      (by omega) hp2
    refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2, if_pos hab], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨eC, q, hq, hCc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, hr1]
      obtain ⟨q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨eBy, q, hq, hByc, hq1, by omega⟩
  · have hw : Nat.bits a ≠ Nat.bits b := fun h => hab (hiff.mp h)
    rw [if_neg hw] at hr1
    obtain ⟨hr2, hm2⟩ := eqB_run P oracle r₁ r₂ hne c _ h₁ eBn no hBn hBnc (p + 1).toNat p
      (by omega) hp2
    refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2, if_neg hab], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨eC, q, hq, hCc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, hr1]
      obtain ⟨q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨eBn, q, hq, hBnc, hq1, by omega⟩

end Eq

end Complexity.LogProg
