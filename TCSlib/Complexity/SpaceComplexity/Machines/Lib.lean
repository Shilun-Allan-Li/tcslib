/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.Machines.Bin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Program fragments: binary counters

Reusable pieces of register-tape programs (`Complexity.LogProg.RProg`), each specified by the
transitions it needs at a few states and proved once against the program semantics
`Complexity.LogProg.rstep`. The increment fragment adds one to the binary counter
(`Nat.bits n`, from cell `0`) on a register and returns its head to cell `0`.

## Main definitions

* `Complexity.LogProg.regCfg` — a program configuration with one register changed.
* `Complexity.LogProg.incCAct`, `Complexity.LogProg.incBAct` — the transitions of the
  increment fragment.

## Main results

* `Complexity.LogProg.inc_run` — the increment fragment turns `Nat.bits n` into
  `Nat.bits (n + 1)`, its head staying in `[-1, |Nat.bits (n + 1)|]`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A non-call step of a program is a machine step. -/
lemma rstep_noncall (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (l : Λ) (hl : c.state = some l) (hc : P.call l = none) :
    rstep P oracle c = P.tm.step c := by
  simp [rstep, hl, hc]

/-- Running a program one step is `rstep`. -/
lemma rrun_one (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x) :
    rrun P oracle c 1 = rstep P oracle c := rfl

/-- Running a program zero steps leaves the configuration unchanged. -/
lemma rrun_zero (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x) :
    rrun P oracle c 0 = c := rfl

/-- Running `a + b` steps is running `a` steps, then `b` steps. -/
lemma rrun_add (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (a b : ℕ) : rrun P oracle c (a + b) = rrun P oracle (rrun P oracle c a) b := by
  simp only [rrun]
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- A configuration with state `s` and register `r` holding tape `f` with its head at `p`,
everything else as in `c`. -/
def regCfg (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ) :
    Cfg m Bool Λ x :=
  ⟨some s, c.inputPos, Function.update c.workTapes r f, Function.update c.workTapePos r p,
    c.output⟩

/-- The register view `regCfg c s …` is in state `s`. -/
@[simp] lemma regCfg_state (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool)
    (p : ℤ) : (regCfg c s r f p).state = some s := rfl

/-- An action touching only register `r`. -/
def regAct (r : Fin m) (w : Option (Option Bool)) (mv : SignType) (s : Λ) : Action m Bool Λ :=
  ⟨0, fun r' => if r' = r then (w, mv) else (none, 0), none, some s⟩

/-- Applying a register action to a register view writes the register cell (if asked), moves
the register head by `mv`, and enters `s'`.

**Proof sketch.** Unfold the action's application on a register view: only register `r`'s cell
under the head is written and only its head moves. Compare the tape and head families pointwise
(`Function.update_apply`). -/
lemma apply_regAct (c : Cfg m Bool Λ x) (s s' : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ)
    (w : Option (Option Bool)) (mv : SignType) :
    (regAct r w mv s').apply (regCfg c s r f p) =
      regCfg c s' r (match w with | none => f | some b => Function.update f p b) (p + mv) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (by simp [regAct, regCfg])
  · funext r' z
    simp only [regAct, regCfg, Action.apply]
    by_cases h : r' = r
    · subst h
      cases w with
      | none => simp
      | some b =>
        simp only [Function.update_self, ↓reduceIte]
        rw [Function.update_self]
    · simp [h]
  · funext r'
    simp only [regAct, regCfg, Action.apply]
    by_cases h : r' = r
    · subst h; simp
    · simp [h]

/-- The register view reads register `r` at its head position `p`. -/
lemma regCfg_read (c : Cfg m Bool Λ x) (s : Λ) (r : Fin m) (f : ℤ → Option Bool) (p : ℤ) :
    (regCfg c s r f p).workTapeSymbols r = f p := by
  simp [regCfg, Cfg.workTapeSymbols]

/-- Overwriting the cell right after a prefix. -/
lemma update_bufferTape_cons (pre w : List Bool) (b b' : Bool) :
    Function.update (FinTM.bufferTape (pre ++ b :: w)) (pre.length : ℤ) (some b') =
      FinTM.bufferTape (pre ++ b' :: w) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst hz; simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    simp only [FinTM.bufferTape]
    split_ifs with h0
    · have hne : z.toNat ≠ pre.length := by omega
      rw [List.getElem?_append, List.getElem?_append]
      split_ifs with h3
      · rfl
      · obtain ⟨j, hj⟩ : ∃ j, z.toNat - pre.length = j + 1 :=
          ⟨z.toNat - pre.length - 1, by omega⟩
        rw [hj]; rfl
    · rfl

/-- Writing past the end of a stored word appends. -/
lemma update_bufferTape_end (w : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape w) (w.length : ℤ) (some b) = FinTM.bufferTape (w ++ [b]) :=
  (FinTM.bufferTape_append w b).symm

/-! ## The increment fragment -/

/-- The carry state of the increment: flip `1`s to `0` moving right; at a `0` or the end
write `1`, step back, and return. -/
def incCAct (r : Fin m) (cC cB : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some true => regAct r (some (some false)) 1 cC
  | _ => regAct r (some (some true)) (-1) cB

/-- The return state: walk left to the left blank, then step onto cell `0` and continue. -/
def incBAct (r : Fin m) (cB next : Λ) (rd : Option Bool) : Action m Bool Λ :=
  match rd with
  | some _ => regAct r none (-1) cB
  | none => regAct r none 1 next

section Inc

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m) (cC cB next : Λ)
  (hC : ∀ a w, P.tm.tr cC a w = incCAct r cC cB (w r))
  (hB : ∀ a w, P.tm.tr cB a w = incBAct r cB next (w r))
  (hCc : P.call cC = none) (hBc : P.call cB = none)

include hC hCc in
/-- **The carry phase** of the increment: from `cC` at the start of the suffix `w`, the program
reaches `cB` with `w` replaced by its increment `incW w`, the head in range throughout.

**Proof sketch.** Induction on `w`. A `1` becomes `0` and the carry moves right; a `0`, or the
blank after the word, becomes `1` and ends the carry, entering `cB`. The head stays within
`[|pre|, |pre ++ w|]`. -/
lemma incC_run (c : Cfg m Bool Λ x) :
    ∀ (w pre : List Bool), ∃ (T : ℕ) (p : ℤ), -1 ≤ p ∧ p < (pre ++ incW w).length ∧
      rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ w)) pre.length) T =
        regCfg c cB r (FinTM.bufferTape (pre ++ incW w)) p ∧
      ∀ t < T, ∃ f q, rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ w)) pre.length) t =
        regCfg c cC r f q ∧ (pre.length : ℤ) ≤ q ∧ q ≤ (pre ++ w).length := by
  intro w
  induction w with
  | nil =>
    intro pre
    refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [incW]; omega, ?_, ?_⟩
    · rw [rrun_one]
      rw [rstep_noncall P oracle _ cC rfl hCc]
      unfold MultiTapeTM.step
      simp only [regCfg_state]
      rw [hC, regCfg_read]
      have hrd : FinTM.bufferTape (pre ++ []) (pre.length : ℤ) = none := by simp
      rw [hrd]
      simp only [incCAct]
      rw [apply_regAct]
      dsimp only
      simp only [List.append_nil, incW]
      rw [update_bufferTape_end]
      simp only [SignType.coe_neg_one, sub_eq_add_neg]
    · intro t ht
      obtain rfl : t = 0 := by omega
      exact ⟨_, _, rfl, le_rfl, by simp⟩
  | cons b w ih =>
    intro pre
    cases b with
    | false =>
      refine ⟨1, (pre.length : ℤ) - 1, by omega, by simp [incW]; omega, ?_, ?_⟩
      · rw [rrun_one]
        rw [rstep_noncall P oracle _ cC rfl hCc]
        unfold MultiTapeTM.step
        simp only [regCfg_state]
        rw [hC, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ false :: w) (pre.length : ℤ) = some false := by simp
        rw [hrd]
        simp only [incCAct]
        rw [apply_regAct]
        dsimp only
        simp only [incW]
        rw [update_bufferTape_cons]
        simp only [SignType.coe_neg_one, sub_eq_add_neg]
      · intro t ht
        obtain rfl : t = 0 := by omega
        exact ⟨_, _, rfl, le_rfl, by simp; omega⟩
    | true =>
      obtain ⟨T, p, hp1, hp2, hrun, hmid⟩ := ih (pre ++ [false])
      have hstep : rrun P oracle (regCfg c cC r (FinTM.bufferTape (pre ++ true :: w)) pre.length) 1 =
          regCfg c cC r (FinTM.bufferTape (pre ++ [false] ++ w)) (pre ++ [false]).length := by
        rw [rrun_one]
        rw [rstep_noncall P oracle _ cC rfl hCc]
        unfold MultiTapeTM.step
        simp only [regCfg_state]
        rw [hC, regCfg_read]
        have hrd : FinTM.bufferTape (pre ++ true :: w) (pre.length : ℤ) = some true := by simp
        rw [hrd]
        simp only [incCAct]
        rw [apply_regAct]
        dsimp only
        rw [update_bufferTape_cons]
        simp
      refine ⟨1 + T, p, hp1, by simpa [incW] using hp2, ?_, ?_⟩
      · rw [rrun_add, hstep, hrun]; simp [incW]
      · intro t ht
        rcases Nat.lt_or_ge t 1 with h | h
        · obtain rfl : t = 0 := by omega
          exact ⟨_, _, rfl, le_rfl, by simp; omega⟩
        · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
          rw [rrun_add, hstep]
          obtain ⟨f, q, hq, h1, h2⟩ := hmid t' (by omega)
          exact ⟨f, q, hq, by simp at h1 ⊢; omega, by simp at h2 ⊢; omega⟩

include hB hBc in
/-- **The return phase** of the increment: from `cB` at position `p < |w|`, the head walks left to
the left blank and back onto cell `0`, entering `next`.

**Proof sketch.** Induction on `n = p + 1`: on a letter the head moves left; at the left blank
`-1` it moves right onto cell `0` and the state becomes `next`. -/
lemma incB_run (c : Cfg m Bool Λ x) (w : List Bool) :
    ∀ (n : ℕ) (p : ℤ), p + 1 = n → p < w.length →
      rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) (n + 1) =
        regCfg c next r (FinTM.bufferTape w) 0 ∧
      ∀ t < n + 1, ∃ q, rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) t =
        regCfg c cB r (FinTM.bufferTape w) q ∧ -1 ≤ q ∧ q ≤ p := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    refine ⟨?_, fun t ht => ?_⟩
    swap
    · obtain rfl : t = 0 := by omega
      exact ⟨p, rfl, by omega, le_rfl⟩
    rw [rrun_one]
    rw [rstep_noncall P oracle _ cB rfl hBc]
    unfold MultiTapeTM.step
    simp only [regCfg_state]
    rw [hB, regCfg_read]
    have hrd : FinTM.bufferTape w p = none := by rw [show p = -1 by omega]; simp
    rw [hrd]
    simp only [incBAct]
    rw [apply_regAct]
    try congr 1
  | succ n ih =>
    intro p hp hpw
    obtain ⟨j, hj⟩ : ∃ j : ℕ, p = j := ⟨p.toNat, by omega⟩
    have hjw : j < w.length := by omega
    have hstep : rrun P oracle (regCfg c cB r (FinTM.bufferTape w) p) 1 =
        regCfg c cB r (FinTM.bufferTape w) (p - 1) := by
      rw [rrun_one]
      rw [rstep_noncall P oracle _ cB rfl hBc]
      unfold MultiTapeTM.step
      simp only [regCfg_state]
      rw [hB, regCfg_read]
      have hrd : FinTM.bufferTape w p = some w[j] := by
        rw [hj]; simp [List.getElem?_eq_getElem hjw]
      rw [hrd]
      simp only [incBAct]
      rw [apply_regAct]
      try congr 1
    obtain ⟨ihr, ihm⟩ := ih (p - 1) (by omega) (by omega)
    refine ⟨?_, fun t ht => ?_⟩
    · rw [show n + 1 + 1 = 1 + (n + 1) by ring, rrun_add, hstep, ihr]
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨p, rfl, by omega, le_rfl⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, hstep]
        obtain ⟨q, hq, h1, h2⟩ := ihm t' (by omega)
        exact ⟨q, hq, h1, by omega⟩

include hC hB hCc hBc in
/-- **The increment fragment**: from `cC` with `Nat.bits n` on register `r` and its head on
cell `0`, the program reaches `next` with `Nat.bits (n + 1)` there and its head on cell `0`,
everything else unchanged; on the way it is only in the fragment's (non-call) states, with
the head of `r` in `[-1, |Nat.bits (n + 1)|]`.

**Proof sketch.** Run the carry phase (`incC_run`) from cell `0`, which turns `bits n` into
`incW (bits n) = bits (n + 1)` (`bits_succ`). Then run the return phase (`incB_run`) back to
cell `0`; the head ranges of the two phases combine. -/
lemma inc_run (c : Cfg m Bool Λ x) (n : ℕ) :
    ∃ T, rrun P oracle (regCfg c cC r (FinTM.bufferTape (Nat.bits n)) 0) T =
        regCfg c next r (FinTM.bufferTape (Nat.bits (n + 1))) 0 ∧
      ∀ t < T, ∃ s f q, rrun P oracle (regCfg c cC r (FinTM.bufferTape (Nat.bits n)) 0) t =
        regCfg c s r f q ∧ (s = cC ∨ s = cB) ∧ -1 ≤ q ∧ q ≤ (Nat.bits (n + 1)).length := by
  obtain ⟨T₁, p, hp1, hp2, hr1, hm1⟩ := incC_run P oracle r cC cB hC hCc c (Nat.bits n) []
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hp2 hr1 hm1
  rw [← bits_succ] at hp2 hr1
  obtain ⟨hr2, hm2⟩ := incB_run P oracle r cB next hB hBc c (Nat.bits (n + 1)) (p + 1).toNat p
    (by omega) hp2
  refine ⟨T₁ + ((p + 1).toNat + 1), by rw [rrun_add, hr1, hr2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · obtain ⟨f, q, hq, h1, h2⟩ := hm1 t h
    have hl : (Nat.bits n).length ≤ (Nat.bits (n + 1)).length := by
      rw [bits_succ]
      generalize Nat.bits n = w
      induction w with
      | nil => simp [incW]
      | cons b w ih => cases b <;> simp [incW, ih]
    exact ⟨cC, f, q, hq, Or.inl rfl, by omega, by omega⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, hr1]
    obtain ⟨q, hq, h1, h2⟩ := hm2 t' (by omega)
    exact ⟨cB, _, q, hq, Or.inr rfl, h1, by omega⟩

end Inc

end Complexity.LogProg
