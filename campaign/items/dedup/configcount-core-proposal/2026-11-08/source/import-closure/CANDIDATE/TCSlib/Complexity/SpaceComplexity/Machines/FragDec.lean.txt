/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Lib

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: decrement and clear

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Frag`: words without trailing
`0`, the decrement fragment, the walk to the right end of a register word and the clear
fragment.

## Main definitions

* `Complexity.LogProg.decW` — the decrement of a little-endian word.

## Main results

* `Complexity.LogProg.dec_run` — `Nat.bits n ↦ Nat.bits (n - 1)`.
* `Complexity.LogProg.toEnd_run` — the walk to the right end of a word.
* `Complexity.LogProg.clr_run` — `Nat.bits n ↦ Nat.bits 0`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## Words -/

/-- The decrement of a little-endian word (borrow propagation, dropping a final `0`). -/
def decW : List Bool → List Bool
  | [] => []
  | false :: w => true :: decW w
  | [true] => []
  | true :: b :: w => false :: b :: w

/-- A word without a trailing `0`. -/
def Canon (w : List Bool) : Prop := ∀ h : w ≠ [], w.getLast h = true

/-- The binary word of a number has no trailing `0`. -/
lemma canon_bits (n : ℕ) : Canon (Nat.bits n) := fun h => bits_getLast n h

/-- A word without trailing `0` keeps that property when its first letter is dropped. -/
lemma canon_tail {b : Bool} {w : List Bool} (h : Canon (b :: w)) : Canon w := by
  intro hw
  have := h (by simp)
  rwa [List.getLast_cons hw] at this

/-- Decrementing the increment of a word without trailing `0` gives the word back. -/
lemma decW_incW (w : List Bool) (h : Canon w) : decW (incW w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false =>
      cases w with
      | nil => have := h (by simp); simp at this
      | cons c w => rfl
    | true => simp only [incW, decW]; rw [ih (canon_tail h)]

/-- The binary word of `n - 1` is the decrement of that of `n`. -/
lemma bits_pred (n : ℕ) : Nat.bits (n - 1) = decW (Nat.bits n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.zero_bits, decW]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, bits_succ, decW_incW _ (canon_bits k)]

/-- The binary word of `n / 2` is the tail of that of `n`. -/
lemma bits_half (n : ℕ) : Nat.bits (n / 2) = (Nat.bits n).tail := by
  rw [← Nat.div2_val, Nat.div2_bits_eq_tail]

/-- The parity of `n` is its first binary digit. -/
lemma bits_head_odd (n : ℕ) : (Nat.bits n).head? = if n = 0 then none else some (decide (n % 2 = 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.zero_bits]
  · have hdecomp : n = 2 * (n / 2) + (decide (n % 2 = 1)).toNat := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
    have hb : n / 2 = 0 → decide (n % 2 = 1) = true := by intro h0; simp; omega
    have e := bits_two_mul_add (n / 2) _ hb
    rw [← hdecomp] at e
    rw [e]; simp [show n ≠ 0 by omega]

/-- Erasing the last cell of a buffer tape holding `pre ++ [b]` leaves a buffer tape holding
`pre`. -/
lemma bufferTape_erase_last (pre : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape (pre ++ [b])) (pre.length : ℤ) none =
      FinTM.bufferTape pre := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst hz; simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    simp only [FinTM.bufferTape]
    split_ifs with h0
    · by_cases h1 : z.toNat < pre.length
      · rw [List.getElem?_append_left h1]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · rfl

/-! ## The decrement fragment -/

/-- The borrow state: `0`s become `1`s moving right; the first `1` becomes `0` and the next
cell decides whether it was the last bit. -/
def decDAct {m : ℕ} {Λ : Type} (r : Fin m) (dD dL dB : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | some false => regAct r (some (some true)) 1 dD
  | some true => regAct r (some (some false)) 1 dL
  | none => regAct r none (-1) dB

/-- The lookahead after the borrow: a blank means the new `0` is a trailing zero. -/
def decLAct {m : ℕ} {Λ : Type} (r : Fin m) (dE dB : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | none => regAct r none (-1) dE
  | some _ => regAct r none (-1) dB

/-- Erase the trailing zero. -/
def decEAct {m : ℕ} {Λ : Type} (r : Fin m) (dB : Λ) : Action m Bool Λ :=
  regAct r (some none) (-1) dB

section Dec

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (dD dL dE dB next : Λ)
  (hD : ∀ a w, P.tm.tr dD a w = decDAct r dD dL dB (w r))
  (hL : ∀ a w, P.tm.tr dL a w = decLAct r dE dB (w r))
  (hE : ∀ a w, P.tm.tr dE a w = decEAct r dB)
  (hB : ∀ a w, P.tm.tr dB a w = incBAct r dB next (w r))
  (hDc : P.call dD = none) (hLc : P.call dL = none) (hEc : P.call dE = none)
  (hBc : P.call dB = none)

/-- Peel the first step off a run. -/
lemma rrun_succ_left (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (n : ℕ) : rrun P oracle c (n + 1) = rrun P oracle (rrun P oracle c 1) n := by
  rw [Nat.add_comm, rrun_add]

/-- One ordinary step of a program from a `regCfg`. -/
lemma rrun_one_reg (c : Cfg m Bool Λ x) (s : Λ) (f : ℤ → Option Bool) (p : ℤ)
    (hs : P.call s = none) :
    rrun P oracle (regCfg c s r f p) 1 =
      (P.tm.tr s (regCfg c s r f p).inputSymbol (regCfg c s r f p).workTapeSymbols).apply
        (regCfg c s r f p) := by
  rw [rrun_one, rstep_noncall P oracle _ s rfl hs]
  unfold MultiTapeTM.step
  simp only [regCfg_state]

include hD hL hE hDc hLc hEc in
/-- **The borrow phase** of the decrement: from `dD` with the head at the start of the suffix `w`
(no trailing `0`), the program reaches `dB` with `w` replaced by its decrement `decW w`, the
head in range throughout.

**Proof sketch.** Induction on `w`. A leading `0` becomes `1` and the borrow moves right; a
leading `1` becomes `0` and ends the borrow. If that `1` was the last letter, the trailing `0`
is erased through `dL`/`dE`. The head stays within `[|pre|, |pre ++ w|]`. -/
lemma decD_run (c : Cfg m Bool Λ x) :
    ∀ (w pre : List Bool), Canon w → ∃ (T : ℕ) (p : ℤ), -1 ≤ p ∧ p < (pre ++ decW w).length ∧
      rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ w)) pre.length) T =
        regCfg c dB r (FinTM.bufferTape (pre ++ decW w)) p ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ w)) pre.length) t =
        regCfg c s r f q ∧ (s = dD ∨ s = dL ∨ s = dE) ∧ (pre.length : ℤ) ≤ q ∧
          q ≤ (pre ++ w).length := by
  intro w
  induction w with
  | nil =>
    intro pre _
    refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [decW], ?_, ?_⟩
    · rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
      have hrd : FinTM.bufferTape (pre ++ []) (pre.length : ℤ) = none := by simp
      rw [hrd]
      simp only [decDAct]
      rw [apply_regAct]
      simp [decW, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp⟩
  | cons b w ih =>
    intro pre hcan
    cases b with
    | false =>
      obtain ⟨T, p, hp1, hp2, hrun, hmid⟩ := ih (pre ++ [true]) (canon_tail hcan)
      have hstep : rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ false :: w))
          pre.length) 1 =
          regCfg c dD r (FinTM.bufferTape (pre ++ [true] ++ w)) (pre ++ [true]).length := by
        rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ false :: w) (pre.length : ℤ) = some false := by
          simp
        rw [hrd]
        simp only [decDAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      refine ⟨1 + T, p, hp1, by simpa [decW] using hp2, ?_, ?_⟩
      · rw [rrun_add, hstep, hrun]; simp [decW]
      · intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨s, f, q, hq, hs, h1, h2⟩ := hmid t' (by omega)
          exact ⟨s, f, q, hq, hs, by simp at h1 ⊢; omega, by simp at h2 ⊢; omega⟩
    | true =>
      have hstep : rrun P oracle (regCfg c dD r (FinTM.bufferTape (pre ++ true :: w))
          pre.length) 1 =
          regCfg c dL r (FinTM.bufferTape (pre ++ false :: w)) ((pre.length : ℤ) + 1) := by
        rw [rrun_one_reg P oracle r c dD _ _ hDc, hD, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ true :: w) (pre.length : ℤ) = some true := by simp
        rw [hrd]
        simp only [decDAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      cases w with
      | nil =>
        -- the last bit: erase it
        have hstep2 : rrun P oracle (regCfg c dL r (FinTM.bufferTape (pre ++ [false]))
            ((pre.length : ℤ) + 1)) 1 =
            regCfg c dE r (FinTM.bufferTape (pre ++ [false])) pre.length := by
          rw [rrun_one_reg P oracle r c dL _ _ hLc, hL, regCfg_read]
          have hrd : FinTM.bufferTape (pre ++ [false]) ((pre.length : ℤ) + 1) = none := by
            simp [FinTM.bufferTape]
          rw [hrd]
          simp only [decLAct]
          rw [apply_regAct]
          simp
        have hstep3 : rrun P oracle (regCfg c dE r (FinTM.bufferTape (pre ++ [false]))
            pre.length) 1 = regCfg c dB r (FinTM.bufferTape pre) ((pre.length : ℤ) - 1) := by
          rw [rrun_one_reg P oracle r c dE _ _ hEc, hE]
          simp only [decEAct]
          rw [apply_regAct]
          dsimp only
          rw [bufferTape_erase_last]
          simp [sub_eq_add_neg]
        refine ⟨1 + (1 + 1), (pre.length : ℤ) - 1, by omega, by simp [decW], ?_, ?_⟩
        · rw [rrun_add, hstep, rrun_add, hstep2, hstep3]; simp [decW]
        · intro t ht
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp⟩
          rw [show t = 1 + (t - 1) by omega, rrun_add, hstep]
          rcases Nat.lt_or_ge (t - 1) 1 with h' | h'
          · rw [show t - 1 = 0 by omega]
            exact ⟨_, _, _, rfl, Or.inr (Or.inl rfl), by omega, by simp⟩
          · rw [show t - 1 = 1 + 0 by omega, rrun_add, hstep2]
            exact ⟨_, _, _, rfl, Or.inr (Or.inr rfl), le_rfl, by simp⟩
      | cons b' w' =>
        have hstep2 : rrun P oracle (regCfg c dL r (FinTM.bufferTape (pre ++ false :: b' :: w'))
            ((pre.length : ℤ) + 1)) 1 =
            regCfg c dB r (FinTM.bufferTape (pre ++ false :: b' :: w')) pre.length := by
          rw [rrun_one_reg P oracle r c dL _ _ hLc, hL, regCfg_read]
          have hrd : FinTM.bufferTape (pre ++ false :: b' :: w') ((pre.length : ℤ) + 1) =
              some b' := by
            simp only [FinTM.bufferTape]
            rw [if_pos (by omega), show ((pre.length : ℤ) + 1).toNat = pre.length + 1 by omega]
            simp
          rw [hrd]
          simp only [decLAct]
          rw [apply_regAct]
          simp
        refine ⟨1 + 1, pre.length, by omega, by simp [decW]; omega, ?_, ?_⟩
        · rw [rrun_add, hstep, hstep2]; simp [decW]
        · intro t ht
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨_, _, _, rfl, Or.inl rfl, le_rfl, by simp; omega⟩
          · obtain rfl : t = 1 := by omega
            rw [hstep]
            exact ⟨_, _, _, rfl, Or.inr (Or.inl rfl), by omega, by simp; omega⟩

include hD hL hE hB hDc hLc hEc hBc in
/-- **The decrement fragment**: `Nat.bits n ↦ Nat.bits (n - 1)` on register `r`, head back on
cell `0`, head in `[-1, |Nat.bits n|]` throughout.

**Proof sketch.** For `n = 0` the word is empty and the fragment returns at once. Otherwise run
the borrow phase (`decD_run`), which replaces `bits n` by `decW (bits n) = bits (n - 1)`
(`decW_incW`, `bits_succ`). Then run the return walk to cell `0`; the head ranges combine. -/
lemma dec_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c dD r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n - 1))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c dD r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := decD_run P oracle r dD dL dE dB hD hL hE hDc hLc hEc c
    (Nat.bits n) [] (canon_bits n)
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hp2 hr1 hm1
  rw [← bits_pred] at hp2 hr1
  obtain ⟨hr2, hm2⟩ := incB_run P oracle r dB next hB hBc c (Nat.bits (n - 1)) (p + 1).toNat p
    (by omega) hp2
  have hlen : (Nat.bits (n - 1)).length ≤ (Nat.bits n).length := by
    exact length_bits_mono (by omega)
  refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · obtain ⟨s, f, q, hq, hs, h1, h2⟩ := hm1 t h
    exact ⟨s, f, q, hq, by rcases hs with rfl | rfl | rfl <;> assumption, by omega, h2⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, hr1]
    obtain ⟨q, hq, h1, h2⟩ := hm2 t' (by omega)
    exact ⟨dB, _, q, hq, hBc, h1, by omega⟩

end Dec

/-! ## Walking to the right end -/

/-- Walk right over the word; at its right end step back and continue in `nx`. -/
def toEndAct {m : ℕ} {Λ : Type} (r : Fin m) (cR nx : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some _ => regAct r none 1 cR
  | none => regAct r none (-1) nx

section ToEnd

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (cR nx : Λ)
  (hR : ∀ a w, P.tm.tr cR a w = toEndAct r cR nx (w r)) (hRc : P.call cR = none)

include hR hRc in
/-- **The walk to the right end** of a register word: from `cR` at position `p ≥ 0` the head moves
right to the blank after `w`, then back onto the last letter, entering `nx`.

**Proof sketch.** Induction on `n = |w| - p`: on a letter the head moves right; on the blank at
`|w|` it moves left and the state becomes `nx`. The head stays in `[p, |w|]`. -/
lemma toEnd_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ (n : ℕ) (p : ℤ), (w.length : ℤ) - p = n → 0 ≤ p →
      rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) (n + 1) =
        regCfg c nx r (FinTM.bufferTape w) ((w.length : ℤ) - 1) ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) t =
        regCfg c cR r (FinTM.bufferTape w) q ∧ p ≤ q ∧ q ≤ w.length := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    have hpw : p = w.length := by omega
    refine ⟨?_, fun t ht => ⟨p, by obtain rfl : t = 0 := by omega
                                   rfl, le_rfl, by omega⟩⟩
    rw [rrun_one_reg P oracle r c cR _ _ hRc, hR, regCfg_read]
    have hrd : FinTM.bufferTape w p = none := by rw [hpw]; simp
    rw [hrd]
    simp only [toEndAct]
    rw [apply_regAct]
    simp [hpw, sub_eq_add_neg]
  | succ n ih =>
    intro p hp h0
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w.length := by omega
    have hstep : rrun P oracle (regCfg c cR r (FinTM.bufferTape w) p) 1 =
        regCfg c cR r (FinTM.bufferTape w) (p + 1) := by
      rw [rrun_one_reg P oracle r c cR _ _ hRc, hR, regCfg_read]
      have hrd : FinTM.bufferTape w p = some w[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [toEndAct]
      rw [apply_regAct]
      simp
    obtain ⟨ihr, ihm⟩ := ih (p + 1) (by omega) (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show n + 1 + 1 = 1 + (n + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨p, rfl, le_rfl, by omega⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨q, hq, by omega, h2⟩

end ToEnd

/-! ## The clear fragment -/

/-- Erase walking left; at the left blank step onto cell `0` and continue. -/
def clrEAct {m : ℕ} {Λ : Type} (r : Fin m) (cE next : Λ) (rd : Option Bool) :
    Action m Bool Λ :=
  match rd with
  | some _ => regAct r (some none) (-1) cE
  | none => regAct r none 1 next

section Clr

variable {m d : ℕ} {Λ : Type} {x : List Bool} (P : RProg m d Λ)
  (oracle : Fin d → List Bool → Bool) (r : Fin m) (cR cE next : Λ)
  (hR : ∀ a w, P.tm.tr cR a w = toEndAct r cR cE (w r))
  (hE : ∀ a w, P.tm.tr cE a w = clrEAct r cE next (w r))
  (hRc : P.call cR = none) (hEc : P.call cE = none)

include hE hEc in
/-- **The erasing walk** of the clear fragment: from `cE` on the last letter of `w.take k`, the
program erases the word right to left and reaches `next` on cell `0` of a blank register.

**Proof sketch.** Induction on `k`. Each step erases the cell under the head and moves left; at
the left blank `-1` the head moves right onto cell `0` and the state becomes `next`. -/
lemma clrE_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ k ≤ w.length,
      rrun P oracle (regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1)) (k + 1) =
        regCfg c next r (FinTM.bufferTape []) 0 ∧
      ∀ t < k + 1, ∃ f q, rrun P oracle
        (regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1)) t =
          regCfg c cE r f q ∧ -1 ≤ q ∧ q ≤ (k : ℤ) - 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun t ht => ⟨_, _, by obtain rfl : t = 0 := by omega
                                      rfl, by omega, le_rfl⟩⟩
    rw [rrun_one_reg P oracle r c cE _ _ hEc, hE, regCfg_read]
    have hrd : FinTM.bufferTape (w.take 0) (((0 : ℕ) : ℤ) - 1) = none := by simp
    rw [hrd]
    simp only [clrEAct]
    rw [apply_regAct]
    simp
  | succ k ih =>
    intro hk
    have hkw : k < w.length := by omega
    have htake : w.take (k + 1) = w.take k ++ [w[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hkw]; rfl
    have hlen : (w.take k).length = k := List.length_take_of_le (by omega)
    have hstep : rrun P oracle (regCfg c cE r (FinTM.bufferTape (w.take (k + 1)))
        (((k + 1 : ℕ) : ℤ) - 1)) 1 =
        regCfg c cE r (FinTM.bufferTape (w.take k)) ((k : ℤ) - 1) := by
      rw [rrun_one_reg P oracle r c cE _ _ hEc, hE, regCfg_read]
      have hrd : FinTM.bufferTape (w.take (k + 1)) (((k + 1 : ℕ) : ℤ) - 1) = some w[k] := by
        rw [htake]; simp only [FinTM.bufferTape]
        rw [if_pos (by omega), show (((k + 1 : ℕ) : ℤ) - 1).toNat = (w.take k).length by
          rw [hlen]; omega]
        simp only [List.getElem?_append_right (le_refl _), Nat.sub_self]
        rfl
      rw [hrd]
      simp only [clrEAct]
      rw [apply_regAct]
      dsimp only
      rw [show (((k + 1 : ℕ) : ℤ) - 1) = ((w.take k).length : ℤ) by rw [hlen]; push_cast; ring,
        htake, bufferTape_erase_last, hlen]
      simp [sub_eq_add_neg]
    obtain ⟨ihr, ihm⟩ := ih (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show k + 1 + 1 = 1 + (k + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨_, _, rfl, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨f, q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨f, q, hq, h1, by push_cast at h2 ⊢; omega⟩

include hR hE hRc hEc in
/-- **The clear fragment**: `Nat.bits n ↦ Nat.bits 0` on register `r`, head back on cell `0`,
head in `[-1, |Nat.bits n|]` throughout. -/
lemma clr_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c cR r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits 0)) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c cR r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ P.call s = none ∧ -1 ≤ q ∧ q ≤ (Nat.bits n).length := by
  set w := Nat.bits n
  obtain ⟨h1, hm1⟩ := toEnd_run P oracle r cR cE hR hRc c w w.length 0 (by simp) le_rfl
  obtain ⟨h2, hm2⟩ := clrE_run P oracle r cE next hE hEc c w w.length le_rfl
  rw [List.take_length] at h2 hm2
  refine ⟨w.length + 1 + (w.length + 1), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, h2, Nat.zero_bits]
  · rcases Nat.lt_or_ge t (w.length + 1) with h | h
    · obtain ⟨q, hq, hq1, hq2⟩ := hm1 t h
      exact ⟨cR, _, q, hq, hRc, by omega, hq2⟩
    · obtain ⟨t', rfl⟩ : ∃ t', t = w.length + 1 + t' := ⟨t - (w.length + 1), by omega⟩
      rw [rrun_add, h1]
      obtain ⟨f, q, hq, hq1, hq2⟩ := hm2 t' (by omega)
      exact ⟨cE, f, q, hq, hEc, hq1, by omega⟩

end Clr

end Complexity.LogProg
