/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Parse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Format check of inputs `⟨1ⁿ, ⟨u, w⟩⟩`

The pair-format companion of `TCSlib.Complexity.SpaceComplexity.Machines.Parse`: the format
check of inputs `⟨1ⁿ, ⟨u, w⟩⟩`. The comparisons of a register with `u` and `w` are in
`TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp`.

## Main definitions

* `Complexity.LogProg.scanPairs` — the pair scan of the format check, as a function.

## Main results

* `Complexity.LogProg.valPair_run` — the pair format check.

File size: about 650 lines, over the 600-line target. The pair format check is a single
fragment whose phases share their transition hypotheses, and the comparisons on pair inputs
are already split off into `TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-! ## The pair scan as a function -/

/-- Scan aligned pairs `bb` until the separator `01`, remembering the last bit; succeed with
the rest of the word if the separator comes and the last bit was not `0`. -/
def scanPairs : Option Bool → List Bool → Option (List Bool)
  | last, false :: true :: rest => if last = some false then none else some rest
  | _, false :: false :: rest => scanPairs (some false) rest
  | _, true :: true :: rest => scanPairs (some true) rest
  | _, _ => none

/-- Prepending a letter does not change the last letter of a nonempty word. -/
lemma getLast?_cons_of {b v : Bool} {u : List Bool} (h : u.getLast? = some v) :
    (b :: u).getLast? = some v := by
  cases u with
  | nil => simp at h
  | cons c u => rw [List.getLast?_cons_cons]; exact h

/-- The pair scan from state `last` succeeds with rest `w` exactly when the word is `dbl u`,
the separator `01`, then `w`, and the last letter of `u` (or `last` if `u` is empty) is not
`0`.

**Proof sketch.** Induction on `z` following the definition of `scanPairs`. On `0 1` the scan
stops with `u = []`. On `b b` it continues with `b` remembered, and the decomposition of the
rest extends `u` by `b` (`getLast?_cons_of`). Any other start fails on both sides. -/
lemma scanPairs_iff (last : Option Bool) (z w : List Bool) :
    scanPairs last z = some w ↔
      ∃ u, z = dbl u ++ [false, true] ++ w ∧ (u.getLast? <|> last) ≠ some false := by
  constructor
  · intro h
    induction z using List.twoStepInduction generalizing last with
    | nil => simp [scanPairs] at h
    | singleton b => cases b <;> simp [scanPairs] at h
    | cons_cons b b' rest ih _ =>
      cases b <;> cases b' <;> simp only [scanPairs] at h
      · obtain ⟨u, rfl, hu⟩ := ih (some false) h
        refine ⟨false :: u, by simp, ?_⟩
        cases hl : u.getLast? with
        | none => simp_all
        | some v => rw [getLast?_cons_of hl]; simp_all
      · split_ifs at h with hl
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨[], by simp, by simpa using hl⟩
      · simp at h
      · obtain ⟨u, rfl, hu⟩ := ih (some true) h
        refine ⟨true :: u, by simp, ?_⟩
        cases hl : u.getLast? with
        | none => simp_all
        | some v => rw [getLast?_cons_of hl]; simp_all
  · rintro ⟨u, rfl, hu⟩
    induction u generalizing last with
    | nil => simp only [dbl_nil, List.nil_append, List.cons_append, scanPairs]; simpa using hu
    | cons b u ih =>
      cases b <;> simp only [dbl_cons, List.cons_append, scanPairs] <;> apply ih <;>
        (cases hl : u.getLast? with
          | none => simp_all
          | some v => rw [getLast?_cons_of hl] at hu; simp_all)

/-! ## Machine phases of the format checks -/

/-- A rejected run: halted with `0` appended, the register head of `r` at `p`, through non-call
states of shape `xCfg`. -/
def Rejects (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c₀ c : Cfg m Bool Λ x)
    (r : Fin m) (p : ℤ) : Prop :=
  ∃ T, (rrun P oracle c₀ T).state = none ∧ (rrun P oracle c₀ T).output = c.output ++ [false] ∧
    (rrun P oracle c₀ T).workTapePos = Function.update c.workTapePos r p ∧
    ∀ t < T, ∃ s ip, rrun P oracle c₀ t = xCfg c s ip r p ∧ P.call s = none

/-- A run reaching a configuration, through non-call states of shape `xCfg`. -/
def Reaches (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c₀ c₁ c : Cfg m Bool Λ x)
    (r : Fin m) (p : ℤ) : Prop :=
  ∃ T, rrun P oracle c₀ T = c₁ ∧
    ∀ t < T, ∃ s ip, rrun P oracle c₀ t = xCfg c s ip r p ∧ P.call s = none

section Phases

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)

/-- Prepend a step to a reaching run. -/
lemma Reaches.step {c₀ c₁ c₂ c : Cfg m Bool Λ x} {p : ℤ} (s : Λ) (ip : Fin (x.length + 2))
    (h₀ : c₀ = xCfg c s ip r p) (hs : P.call s = none) (h1 : rrun P oracle c₀ 1 = c₁)
    (h : Reaches P oracle c₁ c₂ c r p) : Reaches P oracle c₀ c₂ c r p := by
  obtain ⟨T, hT, hm⟩ := h
  refine ⟨1 + T, by rw [rrun_add, h1, hT], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t 1 with h' | h'
  · obtain rfl : t = 0 := by omega
    exact ⟨s, ip, h₀, hs⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h1]; exact hm t' (by omega)

/-- Prepend a step to a rejecting run. -/
lemma Rejects.step {c₀ c₁ c : Cfg m Bool Λ x} {p : ℤ} (s : Λ) (ip : Fin (x.length + 2))
    (h₀ : c₀ = xCfg c s ip r p) (hs : P.call s = none) (h1 : rrun P oracle c₀ 1 = c₁)
    (h : Rejects P oracle c₁ c r p) : Rejects P oracle c₀ c r p := by
  obtain ⟨T, e1, e2, e3, hm⟩ := h
  refine ⟨1 + T, by rw [rrun_add, h1]; exact e1, by rw [rrun_add, h1]; exact e2,
    by rw [rrun_add, h1]; exact e3, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t 1 with h' | h'
  · obtain rfl : t = 0 := by omega
    exact ⟨s, ip, h₀, hs⟩
  · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h1]; exact hm t' (by omega)

/-- Concatenate reaching runs. -/
lemma Reaches.trans {c₀ c₁ c₂ c : Cfg m Bool Λ x} {p : ℤ} (h₁ : Reaches P oracle c₀ c₁ c r p)
    (h₂ : Reaches P oracle c₁ c₂ c r p) : Reaches P oracle c₀ c₂ c r p := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- A reaching run followed by a rejecting one rejects. -/
lemma Reaches.rejects {c₀ c₁ c : Cfg m Bool Λ x} {p : ℤ} (h₁ : Reaches P oracle c₀ c₁ c r p)
    (h₂ : Rejects P oracle c₁ c r p) : Rejects P oracle c₀ c r p := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, f1, f2, f3, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1]; exact f1, by rw [rrun_add, e1]; exact f2,
    by rw [rrun_add, e1]; exact f3, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- A one-step rejection. -/
lemma rejects_one {c : Cfg m Bool Λ x} {p : ℤ} (s : Λ) (ip : Fin (x.length + 2))
    (hs : P.call s = none) (htr : ∀ w, P.tm.tr s (inSym x ip.val) w = rejAct) :
    Rejects P oracle (xCfg c s ip r p) c r p := by
  obtain ⟨e1, e2, e3⟩ := rrun_one_rej P oracle c s ip r p hs htr
  refine ⟨1, e1, e2, e3, fun t ht => ?_⟩
  obtain rfl : t = 0 := by omega
  exact ⟨s, ip, rfl, hs⟩

/-- A reflexive reaching run. -/
lemma Reaches.refl (c₀ c : Cfg m Bool Λ x) (p : ℤ) : Reaches P oracle c₀ c₀ c r p :=
  ⟨0, rfl, fun t ht => absurd ht (by omega)⟩

/-- One right move of the input head, as a reaching step. -/
lemma reaches_right {c : Cfg m Bool Λ x} {p : ℤ} (s s' : Λ) (q : ℕ) (hq : q ≤ x.length)
    (hs : P.call s = none) (htr : ∀ w, P.tm.tr s (inSym x q) w = xAct r 1 0 s') :
    rrun P oracle (xCfg c s ⟨q, by omega⟩ r p) 1 = xCfg c s' ⟨q + 1, by omega⟩ r p := by
  rw [rrun_one_x P oracle c s _ r p hs]
  simp only
  rw [htr, apply_xAct]
  congr 1
  · exact Fin.ext (by rw [moveInputPos_pos_val _ (by simp; omega)])
  · simp

end Phases

/-- A word has no trailing `0` iff its last letter (if any) is not `0`. -/
lemma canon_iff (u : List Bool) : Canon u ↔ u.getLast? ≠ some false := by
  constructor
  · intro h hl
    have hne : u ≠ [] := by rintro rfl; simp at hl
    rw [List.getLast?_eq_getLast hne, h hne] at hl; simp at hl
  · intro h hne
    have := List.getLast?_eq_getLast hne
    cases hb : u.getLast hne
    · rw [hb] at this; exact absurd this h
    · rfl

/-- Choosing between `none` and `o` gives `o`. -/
lemma none_orElse' (o : Option Bool) : ((none : Option Bool) <|> o) = o := rfl

section Phases2

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)

/-- The word state remembering the last bit. -/
def wSt (vW0 vWF vWT : Λ) : Option Bool → Λ
  | none => vW0
  | some false => vWF
  | some true => vWT

include P in
/-- **The final-word phase** of a format check: from `vW` at input position `q`, the rest of
the input being `w`, reach `next` (input rewound) if the last bit read (of `w`, else `last`)
is not `0`, and reject otherwise.

**Proof sketch.** Induction on `w`. Each letter moves the input head right and records it as the
last letter (`wSt`). At the end of the input, the state is accepting exactly when the last
letter is not `0`; it then rewinds the input head (`rewind_x`), and otherwise rejects. -/
lemma valWord_run (vW0 vWF vWT rw₁ rw₂ next : Λ)
    (hW0 : ∀ a w, P.tm.tr vW0 a w = valWAct r vWF vWT rw₁ none a)
    (hWF : ∀ a w, P.tm.tr vWF a w = valWAct r vWF vWT rw₁ (some false) a)
    (hWT : ∀ a w, P.tm.tr vWT a w = valWAct r vWF vWT rw₁ (some true) a)
    (h₁ : ∀ a w, P.tm.tr rw₁ a w = xAct r (-1) 0 rw₂)
    (h₂ : ∀ a w, P.tm.tr rw₂ a w = match a with
      | some _ => xAct r (-1) 0 rw₂
      | none => xAct r 1 0 next)
    (cW0 : P.call vW0 = none) (cWF : P.call vWF = none) (cWT : P.call vWT = none)
    (c₁ : P.call rw₁ = none) (c₂ : P.call rw₂ = none) (c : Cfg m Bool Λ x) (p : ℤ) :
    ∀ (w : List Bool) (last : Option Bool) (q : ℕ) (hq : q + w.length = x.length + 1),
      (∀ k, inSym x (q + k) = w[k]?) →
      ((w.getLast? <|> last) ≠ some false →
        Reaches P oracle (xCfg c (wSt vW0 vWF vWT last) ⟨q, by omega⟩ r p)
          (xCfg c next ⟨1, by omega⟩ r p) c r p) ∧
      ((w.getLast? <|> last) = some false →
        Rejects P oracle (xCfg c (wSt vW0 vWF vWT last) ⟨q, by omega⟩ r p) c r p) := by
  have htr : ∀ (l : Option Bool) a ww, P.tm.tr (wSt vW0 vWF vWT l) a ww =
      valWAct r vWF vWT rw₁ l a := by
    intro l a ww; rcases l with _ | _ | _
    · exact hW0 a ww
    · exact hWF a ww
    · exact hWT a ww
  have hcall : ∀ l, P.call (wSt vW0 vWF vWT l) = none := by
    intro l; rcases l with _ | _ | _
    · exact cW0
    · exact cWF
    · exact cWT
  intro w
  induction w with
  | nil =>
    intro last q hq hin
    have hsym : inSym x q = none := by simpa using hin 0
    constructor
    · intro hl
      simp only [List.getLast?_nil, none_orElse'] at hl
      have hstep : rrun P oracle (xCfg c (wSt vW0 vWF vWT last) ⟨q, by omega⟩ r p) 1 =
          xCfg c rw₁ ⟨q, by omega⟩ r p := by
        rw [rrun_one_x P oracle c _ _ r p (hcall last)]
        simp only
        rw [htr, hsym]
        simp only [valWAct, if_neg hl]
        rw [apply_xAct]; simp
      obtain ⟨T, hT, hm⟩ := rewind_x P oracle c r p rw₁ rw₂ next h₁ h₂ c₁ c₂ ⟨q, by omega⟩
      exact Reaches.step P oracle r _ _ rfl (hcall last) hstep
        ⟨T, hT, fun t ht => by obtain ⟨s', ip', h, hc⟩ := hm t ht; exact ⟨s', ip', h, hc⟩⟩
    · intro hl
      simp only [List.getLast?_nil, none_orElse'] at hl
      exact rejects_one P oracle r _ _ (hcall last) (fun ww => by
        rw [htr]; simp only; rw [hsym]; simp [valWAct, hl])
  | cons b w ih =>
    intro last q hq hin
    have hsym : inSym x q = some b := by simpa using hin 0
    have hstep : rrun P oracle (xCfg c (wSt vW0 vWF vWT last) ⟨q, by omega⟩ r p) 1 =
        xCfg c (wSt vW0 vWF vWT (some b)) ⟨q + 1, by simp at hq; omega⟩ r p := by
      rw [reaches_right P oracle r _ (wSt vW0 vWF vWT (some b)) q (by simp at hq; omega)
        (hcall last) (fun ww => by rw [htr, hsym]; simp only [valWAct]; cases b <;> rfl)]
    have hin' : ∀ k, inSym x (q + 1 + k) = w[k]? := fun k => by
      rw [show q + 1 + k = q + (k + 1) by ring, hin]; simp
    obtain ⟨ih1, ih2⟩ := ih (some b) (q + 1) (by simp at hq; omega) hin'
    have hlast : ((b :: w).getLast? <|> last) = (w.getLast? <|> some b) := by
      cases hw : w.getLast? with
      | none =>
        have : w = [] := by simpa using hw
        subst this; simp
      | some v => rw [getLast?_cons_of hw]; simp
    rw [hlast]
    exact ⟨fun h => Reaches.step P oracle r _ _ rfl (hcall last) hstep (ih1 h),
      fun h => Rejects.step P oracle r _ _ rfl (hcall last) hstep (ih2 h)⟩

end Phases2

/-- First symbol of a pair. -/
def valP1Act (r : Fin m) (vP2 : Bool → Λ) (a : Option Bool) : Action m Bool Λ :=
  match a with
  | some b => xAct r 1 0 (vP2 b)
  | none => rejAct

/-- Second symbol of a pair: `bb` continues, `01` ends the pairs (if the last bit was not `0`). -/
def valP2Act (r : Fin m) (vP1F vP1T vW0 : Λ) (last : Option Bool) (b₁ : Bool) (a : Option Bool) :
    Action m Bool Λ :=
  match a with
  | some b₂ =>
    if b₁ = false ∧ b₂ = true then (if last = some false then rejAct else xAct r 1 0 vW0)
    else if b₁ = b₂ then xAct r 1 0 (if b₁ then vP1T else vP1F) else rejAct
  | none => rejAct

section Pairs

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (vP1 : Option Bool → Λ) (vP2 : Bool → Option Bool → Λ) (vW0 : Λ)
  (hP1 : ∀ l a w, P.tm.tr (vP1 l) a w = valP1Act r (fun b => vP2 b l) a)
  (hP2 : ∀ b l a w, P.tm.tr (vP2 b l) a w =
    valP2Act r (vP1 (some false)) (vP1 (some true)) vW0 l b a)
  (cP1 : ∀ l, P.call (vP1 l) = none) (cP2 : ∀ b l, P.call (vP2 b l) = none)

include hP1 hP2 cP1 cP2 in
/-- **The pair phase** of the pair format check follows `scanPairs`.

**Proof sketch.** Induction on `z` following `scanPairs`. The phase reads two input letters at a
time: `b b` continues with `b` remembered, `0 1` ends the pairs (accepting only if the last
letter was not `0`) and moves to the final word, and anything else, or the end of the input,
rejects. -/
lemma valPairs_run (c : Cfg m Bool Λ x) (p : ℤ) :
    ∀ (z : List Bool) (last : Option Bool) (q : ℕ) (hq : q + z.length = x.length + 1),
      (∀ k, inSym x (q + k) = z[k]?) →
      (∀ w, scanPairs last z = some w →
        ∃ hw : q + z.length - w.length < x.length + 2,
          Reaches P oracle (xCfg c (vP1 last) ⟨q, by omega⟩ r p)
            (xCfg c vW0 ⟨q + z.length - w.length, hw⟩ r p) c r p) ∧
      (scanPairs last z = none → Rejects P oracle (xCfg c (vP1 last) ⟨q, by omega⟩ r p) c r p) := by
  intro z
  induction z using List.twoStepInduction with
  | nil =>
    intro last q hq hin
    refine ⟨fun w h => by simp [scanPairs] at h, fun _ => ?_⟩
    exact rejects_one P oracle r _ _ (cP1 last) (fun ww => by
      rw [hP1]; have := hin 0; simp at this; rw [this]; rfl)
  | singleton b =>
    intro last q hq hin
    refine ⟨fun w h => by cases b <;> simp [scanPairs] at h, fun _ => ?_⟩
    have h0 : inSym x q = some b := by simpa using hin 0
    have h1 : inSym x (q + 1) = none := by simpa using hin 1
    have hstep : rrun P oracle (xCfg c (vP1 last) ⟨q, by omega⟩ r p) 1 =
        xCfg c (vP2 b last) ⟨q + 1, by simp at hq; omega⟩ r p :=
      reaches_right P oracle r _ _ q (by simp at hq; omega) (cP1 last)
        (fun ww => by rw [hP1, h0]; rfl)
    exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
      (rejects_one P oracle r _ _ (cP2 b last) (fun ww => by
        rw [hP2]; simp only; rw [h1]; rfl))
  | cons_cons b b' rest ih _ =>
    intro last q hq hin
    simp only [List.length_cons] at hq
    have h0 : inSym x q = some b := by simpa using hin 0
    have h1 : inSym x (q + 1) = some b' := by simpa using hin 1
    have hstep : rrun P oracle (xCfg c (vP1 last) ⟨q, by omega⟩ r p) 1 =
        xCfg c (vP2 b last) ⟨q + 1, by omega⟩ r p :=
      reaches_right P oracle r _ _ q (by omega) (cP1 last) (fun ww => by rw [hP1, h0]; rfl)
    have hin' : ∀ k, inSym x (q + 2 + k) = rest[k]? := fun k => by
      rw [show q + 2 + k = q + (k + 2) by ring, hin]; simp
    cases b <;> cases b'
    · -- `00`
      have hstep2 : rrun P oracle (xCfg c (vP2 false last) ⟨q + 1, by omega⟩ r p) 1 =
          xCfg c (vP1 (some false)) ⟨q + 1 + 1, by omega⟩ r p :=
        reaches_right P oracle r _ _ (q + 1) (by omega) (cP2 false last)
          (fun ww => by rw [hP2, h1]; simp [valP2Act])
      obtain ⟨ih1, ih2⟩ := ih (some false) (q + 2) (by omega) hin'
      simp only [scanPairs]
      refine ⟨fun w h => ?_, fun h => ?_⟩
      · obtain ⟨hw, hr⟩ := ih1 w h
        refine ⟨by simp; omega, ?_⟩
        refine Reaches.step P oracle r _ _ rfl (cP1 last) hstep
          (Reaches.step P oracle r _ _ rfl (cP2 false last) hstep2 ?_)
        convert hr using 3
        simp; omega
      · exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
          (Rejects.step P oracle r _ _ rfl (cP2 false last) hstep2 (ih2 h))
    · -- `01`: the separator
      simp only [scanPairs]
      by_cases hl : last = some false
      · rw [if_pos hl]
        refine ⟨fun w h => by simp at h, fun _ => ?_⟩
        exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
          (rejects_one P oracle r _ _ (cP2 false last) (fun ww => by
            rw [hP2, h1]; simp only [valP2Act, and_self, ↓reduceIte, if_pos hl]))
      · rw [if_neg hl]
        have hstep2 : rrun P oracle (xCfg c (vP2 false last) ⟨q + 1, by omega⟩ r p) 1 =
            xCfg c vW0 ⟨q + 1 + 1, by omega⟩ r p :=
          reaches_right P oracle r _ _ (q + 1) (by omega) (cP2 false last)
            (fun ww => by rw [hP2, h1]; simp [valP2Act, hl])
        refine ⟨fun w h => ?_, fun h => by simp at h⟩
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨by simp; omega, ?_⟩
        refine Reaches.step P oracle r _ _ rfl (cP1 last) hstep
          (Reaches.step P oracle r _ _ rfl (cP2 false last) hstep2 ?_)
        convert Reaches.refl P oracle r _ c p using 3
        simp; omega
    · -- `10`: malformed
      simp only [scanPairs]
      refine ⟨fun w h => by simp at h, fun _ => ?_⟩
      exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
        (rejects_one P oracle r _ _ (cP2 true last) (fun ww => by
          rw [hP2]; simp only; rw [h1]; simp [valP2Act]))
    · -- `11`
      have hstep2 : rrun P oracle (xCfg c (vP2 true last) ⟨q + 1, by omega⟩ r p) 1 =
          xCfg c (vP1 (some true)) ⟨q + 1 + 1, by omega⟩ r p :=
        reaches_right P oracle r _ _ (q + 1) (by omega) (cP2 true last)
          (fun ww => by rw [hP2, h1]; simp [valP2Act])
      obtain ⟨ih1, ih2⟩ := ih (some true) (q + 2) (by omega) hin'
      simp only [scanPairs]
      refine ⟨fun w h => ?_, fun h => ?_⟩
      · obtain ⟨hw, hr⟩ := ih1 w h
        refine ⟨by simp; omega, ?_⟩
        refine Reaches.step P oracle r _ _ rfl (cP1 last) hstep
          (Reaches.step P oracle r _ _ rfl (cP2 true last) hstep2 ?_)
        convert hr using 3
        simp; omega
      · exact Rejects.step P oracle r _ _ rfl (cP1 last) hstep
          (Rejects.step P oracle r _ _ rfl (cP2 true last) hstep2 (ih2 h))

end Pairs

section Prefix

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (vU0 vU1 vS vX : Λ)
  (hU0 : ∀ a w, P.tm.tr vU0 a w = valUAct r vU0 vU1 vS false a)
  (hU1 : ∀ a w, P.tm.tr vU1 a w = valUAct r vU0 vU1 vS true a)
  (hS : ∀ a w, P.tm.tr vS a w = valSAct r vX a)
  (cU0 : P.call vU0 = none) (cU1 : P.call vU1 = none) (cS : P.call vS = none)

include hU0 hU1 hS cU0 cU1 cS in
/-- **The prefix phase** of the format checks: an even run of `1`s, then `0 1`.

**Proof sketch.** Scan the leading run of `1`s keeping its parity in the state (`tRun` letters),
then require `0` and then `1`. If all three conditions hold the run reaches `vX` after `tRun x +
2` letters; otherwise the parity test or one of the two letter tests rejects. -/
lemma valPrefix_run (c : Cfg m Bool Λ x) (p : ℤ) :
    (∀ _h : tRun x % 2 = 0 ∧ x[tRun x]? = some false ∧ x[tRun x + 1]? = some true,
      ∃ hb : 3 + tRun x < x.length + 2,
        Reaches P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (xCfg c vX ⟨3 + tRun x, hb⟩ r p) c r p) ∧
    (¬ (tRun x % 2 = 0 ∧ x[tRun x]? = some false ∧ x[tRun x + 1]? = some true) →
      Rejects P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) c r p) := by
  set t := tRun x with ht
  have htx : t ≤ x.length := tRun_le x
  let st : ℕ → Λ := fun j => if j % 2 = 0 then vU0 else vU1
  have hst : ∀ j, P.call (st j) = none := fun j => by simp only [st]; split_ifs <;> assumption
  have hscan := scanR P oracle c r p st 1 t (by omega) (fun j hj w => by
      rw [show 1 + j = j + 1 by ring, inSym_succ, getElem?_lt_tRun x j hj]
      simp only [st]
      split_ifs with h1 h2 h2
      · omega
      · rw [hU0]; simp [valUAct]
      · rw [hU1]; simp [valUAct]
      · omega)
    (fun j hj => hst j)
  have hU : Reaches P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (xCfg c (st t) ⟨1 + t, by omega⟩ r p)
      c r p :=
    ⟨t, hscan t le_rfl, fun j hj => ⟨st j, _, hscan j hj.le, hst j⟩⟩
  have hsym1 : inSym x (1 + t) = x[t]? := by rw [show 1 + t = t + 1 by ring, inSym_succ]
  have hnotT := getElem?_tRun x
  rw [← ht] at hnotT
  rcases hxt : x[t]? with _ | b
  · refine ⟨fun h => by simp at h, fun _ => hU.rejects P oracle r
      (rejects_one P oracle r _ _ (hst t) (fun w => ?_))⟩
    rw [hsym1, hxt]; simp only [st]; split_ifs
    · rw [hU0]; rfl
    · rw [hU1]; rfl
  cases b with
  | true => exact absurd hxt hnotT
  | false =>
  have htlt : t < x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt; simp at hxt
  by_cases hpar : t % 2 = 0
  swap
  · refine ⟨fun h => absurd h.1 hpar, fun _ => hU.rejects P oracle r
      (rejects_one P oracle r _ _ (hst t) (fun w => ?_))⟩
    rw [hsym1, hxt]; simp only [st, hpar, ↓reduceIte]; rw [hU1]; rfl
  have hS1 : rrun P oracle (xCfg c (st t) ⟨1 + t, by omega⟩ r p) 1 =
      xCfg c vS ⟨1 + t + 1, by omega⟩ r p :=
    reaches_right P oracle r _ _ (1 + t) (by omega) (hst t) (fun w => by
      rw [hsym1, hxt]; simp only [st, hpar, ↓reduceIte]; rw [hU0]; rfl)
  have hUS := hU.trans P oracle r (Reaches.step P oracle r _ _ rfl (hst t) hS1
    (Reaches.refl P oracle r _ c p))
  have hsym2 : inSym x (1 + t + 1) = x[t + 1]? := by rw [show 1 + t + 1 = (t + 1) + 1 by ring,
    inSym_succ]
  rcases hxt1 : x[t + 1]? with _ | b'
  · refine ⟨fun h => by simp at h, fun _ => hUS.rejects P oracle r
      (rejects_one P oracle r _ _ cS (fun w => by rw [hsym2, hxt1, hS]; rfl))⟩
  cases b' with
  | false =>
    refine ⟨fun h => by simp at h, fun _ => hUS.rejects P oracle r
      (rejects_one P oracle r _ _ cS (fun w => by rw [hsym2, hxt1, hS]; rfl))⟩
  | true =>
  have htlt1 : t + 1 < x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hxt1; simp at hxt1
  have hS2 : rrun P oracle (xCfg c vS ⟨1 + t + 1, by omega⟩ r p) 1 =
      xCfg c vX ⟨1 + t + 1 + 1, by omega⟩ r p :=
    reaches_right P oracle r _ _ (1 + t + 1) (by omega) cS (fun w => by
      rw [hsym2, hxt1, hS]; rfl)
  refine ⟨fun _ => ⟨by omega, ?_⟩, fun h => absurd ⟨hpar, rfl, rfl⟩ h⟩
  have := hUS.trans P oracle r (Reaches.step P oracle r _ _ rfl cS hS2
    (Reaches.refl P oracle r _ c p))
  convert this using 3
  omega

end Prefix

/-- An input with a good prefix splits as `⟨1ⁿ, z⟩`.

**Proof sketch.** Split `y` as its leading run `1^{tRun y}`, then `0 1`, then the rest. The run
has even length `2 (tRun y / 2)`, so it is `dbl 1^{tRun y / 2}` (`dbl_replicate`), and the
decomposition is `pairEncode`'s definition. -/
lemma prefix_decomp (y : List Bool) (h0 : tRun y % 2 = 0) (h1 : y[tRun y]? = some false)
    (h2 : y[tRun y + 1]? = some true) :
    y = pairEncode (List.replicate (tRun y / 2) true) (y.drop (tRun y + 2)) := by
  have htake : y.take (tRun y) = List.replicate (tRun y) true := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < tRun y
    · rw [List.getElem?_take, if_pos hi, getElem?_lt_tRun y i hi]; simp [hi]
    · rw [List.getElem?_take, if_neg hi]; simp [hi]
  have hsplit : y = y.take (tRun y) ++ [false, true] ++ y.drop (tRun y + 2) := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_append, List.getElem?_append]
    have hle : tRun y ≤ y.length := tRun_le y
    have hlen : tRun y + 2 ≤ y.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at h2; simp at h2
    by_cases ha : i < tRun y
    · simp [ha, List.length_take, hle, show i < tRun y + 2 by omega,
        List.getElem?_eq_getElem (show i < y.length by omega)]
    · by_cases hb : i < tRun y + 2
      · have : i = tRun y ∨ i = tRun y + 1 := by omega
        rcases this with rfl | rfl
        · simp [h1, hle]
        · simp [h2, hle]
      · simp [hb, hle, List.getElem?_drop]
        congr 1; omega
  rw [pairEncode_eq_dbl, dbl_replicate, show 2 * (tRun y / 2) = tRun y by omega, ← htake]
  exact hsplit

/-- The leading run of `1`s of `⟨1ⁿ, z⟩` has length `2n`. -/
lemma tRun_pairEncode (n : ℕ) (z : List Bool) :
    tRun (pairEncode (List.replicate n true) z) = 2 * n := by
  simp only [tRun, pairEncode_eq_dbl, dbl_replicate, List.append_assoc]
  rw [List.takeWhile_append_of_pos (by simp)]
  simp

/-- The pair format, read off the prefix and the pair scan.

**Proof sketch.** (⇒) On `⟨1ⁿ, ⟨u, w⟩⟩` the prefix is `1²ⁿ 0 1` and the rest is `dbl u 01 w`,
which the pair scan accepts with rest `w` (`scanPairs_iff`). (⇐) Decompose the prefix
(`prefix_decomp`) and the rest (`scanPairs_iff`). The last letter of `u` is not `0`, so `u` has
no trailing `0` (`canon_iff`). -/
lemma validPair_iff (y : List Bool) :
    ValidPair y ↔ (tRun y % 2 = 0 ∧ y[tRun y]? = some false ∧ y[tRun y + 1]? = some true) ∧
      ∃ w, scanPairs none (y.drop (tRun y + 2)) = some w ∧ Canon w := by
  constructor
  · rintro ⟨n, u, w, rfl, hu, hw⟩
    rw [tRun_pairEncode]
    refine ⟨⟨by omega, by simp [pairEncode_eq_dbl, dbl_replicate],
      by simp [pairEncode_eq_dbl, dbl_replicate]⟩, w, ?_, hw⟩
    have hd : (pairEncode (List.replicate n true) (pairEncode u w)).drop (2 * n + 2) =
        dbl u ++ [false, true] ++ w := by
      simp [pairEncode_eq_dbl, dbl_replicate, List.drop_append]
    rw [hd, scanPairs_iff]
    exact ⟨u, rfl, by simpa [none_orElse'] using (canon_iff u).mp hu⟩
  · rintro ⟨⟨h0, h1, h2⟩, w, hs, hw⟩
    obtain ⟨u, hz, hu⟩ := (scanPairs_iff none _ w).mp hs
    refine ⟨tRun y / 2, u, w, ?_, (canon_iff u).mpr (by
      cases hl : u.getLast? <;> simp_all [none_orElse']), hw⟩
    rw [← pairEncode_eq_dbl] at hz
    rw [← hz]
    exact prefix_decomp y h0 h1 h2

section ValPair

variable (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (r : Fin m)
  (vU0 vU1 vS : Λ) (vP1 : Option Bool → Λ) (vP2 : Bool → Option Bool → Λ)
  (vW0 vWF vWT rw₁ rw₂ next : Λ)
  (hU0 : ∀ a w, P.tm.tr vU0 a w = valUAct r vU0 vU1 vS false a)
  (hU1 : ∀ a w, P.tm.tr vU1 a w = valUAct r vU0 vU1 vS true a)
  (hS : ∀ a w, P.tm.tr vS a w = valSAct r (vP1 none) a)
  (hP1 : ∀ l a w, P.tm.tr (vP1 l) a w = valP1Act r (fun b => vP2 b l) a)
  (hP2 : ∀ b l a w, P.tm.tr (vP2 b l) a w =
    valP2Act r (vP1 (some false)) (vP1 (some true)) vW0 l b a)
  (hW0 : ∀ a w, P.tm.tr vW0 a w = valWAct r vWF vWT rw₁ none a)
  (hWF : ∀ a w, P.tm.tr vWF a w = valWAct r vWF vWT rw₁ (some false) a)
  (hWT : ∀ a w, P.tm.tr vWT a w = valWAct r vWF vWT rw₁ (some true) a)
  (h₁ : ∀ a w, P.tm.tr rw₁ a w = xAct r (-1) 0 rw₂)
  (h₂ : ∀ a w, P.tm.tr rw₂ a w = match a with
    | some _ => xAct r (-1) 0 rw₂
    | none => xAct r 1 0 next)
  (cU0 : P.call vU0 = none) (cU1 : P.call vU1 = none) (cS : P.call vS = none)
  (cP1 : ∀ l, P.call (vP1 l) = none) (cP2 : ∀ b l, P.call (vP2 b l) = none)
  (cW0 : P.call vW0 = none) (cWF : P.call vWF = none) (cWT : P.call vWT = none)
  (c₁ : P.call rw₁ = none) (c₂ : P.call rw₂ = none)

include hU0 hU1 hS hP1 hP2 hW0 hWF hWT h₁ h₂ cU0 cU1 cS cP1 cP2 cW0 cWF cWT c₁ c₂ in
/-- **The pair format check**: it reaches `next` (input head back on position `1`) exactly on
inputs `⟨1ⁿ, ⟨u, w⟩⟩` with `u`, `w` free of trailing `0`s, and rejects otherwise.

**Proof sketch.** `valPrefix_run`, then the pair scan `valPairs_run` (which follows
`scanPairs`), then the final word `valWord_run`; `validPair_iff` identifies acceptance. -/
lemma valPair_run (c : Cfg m Bool Λ x) (p : ℤ) :
    (ValidPair x → Reaches P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) (xCfg c next ⟨1, by omega⟩ r p)
      c r p) ∧
    (¬ ValidPair x → Rejects P oracle (xCfg c vU0 ⟨1, by omega⟩ r p) c r p) := by
  have hv := validPair_iff x
  obtain ⟨pre1, pre2⟩ := valPrefix_run P oracle r vU0 vU1 vS (vP1 none) hU0 hU1 hS cU0 cU1 cS c p
  by_cases hpre : tRun x % 2 = 0 ∧ x[tRun x]? = some false ∧ x[tRun x + 1]? = some true
  swap
  · exact ⟨fun h => absurd ((hv.mp h).1) hpre, fun _ => pre2 hpre⟩
  obtain ⟨hb, hr1⟩ := pre1 hpre
  set t := tRun x
  set z := x.drop (t + 2) with hz
  have hlen : t + 2 ≤ x.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hpre; simp at hpre
  have hzlen : 3 + t + z.length = x.length + 1 := by simp [hz]; omega
  have hinz : ∀ k, inSym x (3 + t + k) = z[k]? := by
    intro k; rw [show 3 + t + k = (t + 2 + k) + 1 by ring, inSym_succ, hz, List.getElem?_drop]
  obtain ⟨pp1, pp2⟩ := valPairs_run P oracle r vP1 vP2 vW0 hP1 hP2 cP1 cP2 c p z none (3 + t)
    hzlen hinz
  rcases hs : scanPairs none z with _ | w
  · refine ⟨fun h => ?_, fun _ => hr1.rejects P oracle r (pp2 hs)⟩
    obtain ⟨-, w, hw, -⟩ := hv.mp h
    rw [hs] at hw; simp at hw
  · obtain ⟨hb2, hr2⟩ := pp1 w hs
    obtain ⟨u, hzu, -⟩ := (scanPairs_iff none z w).mp hs
    have hzl : z.length = (dbl u ++ [false, true]).length + w.length := by
      rw [hzu]; simp; omega
    have hinw : ∀ k, inSym x (3 + t + z.length - w.length + k) = w[k]? := by
      intro k
      rw [show 3 + t + z.length - w.length + k = 3 + t + ((dbl u ++ [false, true]).length + k) by
        omega, hinz, hzu, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    obtain ⟨ww1, ww2⟩ := valWord_run P oracle r vW0 vWF vWT rw₁ rw₂ next hW0 hWF hWT h₁ h₂
      cW0 cWF cWT c₁ c₂ c p w none (3 + t + z.length - w.length) (by omega) hinw
    simp only [wSt] at ww1 ww2
    by_cases hcw : Canon w
    · have hok : (w.getLast? <|> none) ≠ some false := by
        cases hl : w.getLast? <;> simp_all [(canon_iff w)]
      refine ⟨fun _ => (hr1.trans P oracle r hr2).trans P oracle r (ww1 hok),
        fun h => absurd (hv.mpr ⟨hpre, w, hs, hcw⟩) h⟩
    · have hbad : (w.getLast? <|> none) = some false := by
        rw [canon_iff] at hcw; push_neg at hcw
        cases hl : w.getLast? <;> simp_all
      refine ⟨fun h => ?_, fun _ => (hr1.trans P oracle r hr2).rejects P oracle r (ww2 hbad)⟩
      obtain ⟨-, w', hw', hc'⟩ := hv.mp h
      rw [hs] at hw'; simp at hw'; subst hw'; exact absurd hc' hcw

end ValPair

end Complexity.LogProg
