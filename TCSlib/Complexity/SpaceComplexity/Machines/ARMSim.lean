/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulating abstract register machines

Each instruction of an abstract register machine (`Complexity.LogProg.ARM`) is simulated by its
fragment in the compiled program (`Complexity.LogProg.armProg`): from the representation
`Complexity.LogProg.aseam` of an abstract configuration the program reaches the
representation of the next one (or halts with the answer), through ordinary states, every
register head in `[-1, W]` when `W` bounds the binary lengths of the values involved.

## Main definitions

* `Complexity.LogProg.Mid` — an ordinary configuration with register heads in `[-1, W]`.
* `Complexity.LogProg.Pre` — the preconditions of an abstract step (distinct registers in
  equality tests, valid inputs for index comparisons, distinct call arguments).

## Main results

* `Complexity.LogProg.arm_step` — one abstract step is simulated.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- An ordinary configuration (not at a call node) with every register head in `[-1, W]`. -/
def Mid (P : RProg m d (Λ × Ph)) (W : ℤ) (c : Cfg m Bool (Λ × Ph) x) : Prop :=
  (∀ s, c.state = some s → P.call s = none) ∧
    ∀ r, -1 ≤ c.workTapePos r ∧ c.workTapePos r ≤ W

/-- The transitions of the compiled program at label `l` are those of the instruction `A l`. -/
lemma armProg_tr (A : ARM m d Λ) (l₀ l : Λ) (ph : Ph) (a : Option Bool) (w : Fin m → Option Bool) :
    (armProg A l₀).tm.tr (l, ph) a w = insTr (A l) l ph a w := rfl

/-- The call nodes of the compiled program at label `l` are those of the instruction `A l`. -/
lemma armProg_call (A : ARM m d Λ) (l₀ l : Λ) (ph : Ph) :
    (armProg A l₀).call (l, ph) = insCall (A l) ph := rfl

/-- The program configuration of values `v` is the register-`r` view of itself, with register
`r` holding the binary word of `v r` and the head at its first cell. -/
lemma aseam_eq_regCfg (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) :
    aseam x l v out = regCfg (aseam x l v out) (l, .start) r
      (FinTM.bufferTape (Nat.bits (v r))) 0 := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r'; by_cases h : r' = r
    · subst h; simp [regCfg, aseam]
    · simp [regCfg, aseam]
  · funext r'; by_cases h : r' = r
    · subst h; simp [regCfg, aseam]
    · simp [regCfg, aseam]

/-- Writing the binary word of `n` into register `r` of the program configuration at `l`, with
the head back at the first cell, gives the program configuration at `l'` with `v r` set to
`n`. -/
lemma regCfg_aseam (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) (n : ℕ) :
    regCfg (aseam x l v out) (l', .start) r (FinTM.bufferTape (Nat.bits n)) 0 =
      aseam x l' (Function.update v r n) out := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r'; by_cases h : r' = r
    · subst h; simp [regCfg, aseam]
    · simp [regCfg, aseam, h]
  · funext r'; by_cases h : r' = r
    · subst h; simp [regCfg, aseam]
    · simp [regCfg, aseam]

/-- A register view of a program configuration, in a non-call phase with the register head
within the register's range, is in the middle of an instruction fragment. -/
lemma mid_regCfg (A : ARM m d Λ) (l₀ : Λ) (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m)
    (s : Λ × Ph) (f : ℤ → Option Bool) (q W : ℤ) (hs : (armProg A l₀).call s = none)
    (hq : -1 ≤ q ∧ q ≤ W) (hW : 0 ≤ W) :
    Mid (armProg A l₀) W (regCfg (aseam x l v out) s r f q) := by
  refine ⟨fun s' h => ?_, fun r' => ?_⟩
  · simp only [regCfg, Option.some.injEq] at h; rw [← h]; exact hs
  · by_cases h : r' = r
    · subst h; simpa [regCfg] using hq
    · simp [regCfg, aseam, h]; omega

/-- An input-scanning view of a program configuration, in a non-call phase with the register
head within the register's range, is in the middle of an instruction fragment. -/
lemma mid_xCfg (A : ARM m d Λ) (l₀ : Λ) (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m)
    (s : Λ × Ph) (ip : Fin (x.length + 2)) (q W : ℤ) (hs : (armProg A l₀).call s = none)
    (hq : -1 ≤ q ∧ q ≤ W) (hW : 0 ≤ W) :
    Mid (armProg A l₀) W (xCfg (aseam x l v out) s ip r q) := by
  refine ⟨fun s' h => ?_, fun r' => ?_⟩
  · simp only [xCfg, Option.some.injEq] at h; rw [← h]; exact hs
  · by_cases h : r' = r
    · subst h; simpa [xCfg] using hq
    · simp [xCfg, aseam, h]; omega

/-- The input-scanning view of a program configuration with the input head at the first cell
and the register head at `0` is the program configuration at the new label. -/
lemma xCfg_aseam (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) :
    xCfg (aseam x l v out) (l', .start) ⟨1, by omega⟩ r 0 = aseam x l' v out := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext r'; by_cases h : r' = r
  · subst h; simp [xCfg, aseam]
  · simp [xCfg, aseam]

/-- A program configuration is its own input-scanning view at the first input cell. -/
lemma xCfg_aseam_self (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) :
    aseam x l v out = xCfg (aseam x l v out) (l, .start) ⟨1, by omega⟩ r 0 :=
  (xCfg_aseam l l v out r).symm

/-- The two-register view of a program configuration with both heads at `0` is the program
configuration at the new label. -/
lemma eqCfg_aseam (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r s : Fin m) :
    eqCfg (aseam x l v out) (l', .start) r s 0 = aseam x l' v out := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext r'
  simp only [eqCfg, aseam, Function.update_apply]
  split_ifs <;> rfl

/-- A simulated run from `c` to `c'` through `Mid` configurations. -/
def SimTo (P : RProg m d (Λ × Ph)) (oracle : Fin d → List Bool → Bool) (W : ℤ)
    (c c' : Cfg m Bool (Λ × Ph) x) : Prop :=
  ∃ T, rrun P oracle c T = c' ∧ ∀ t < T, Mid P W (rrun P oracle c t)

/-- A simulated run from `c` that halts with output `c.output ++ [b]`. -/
def HaltsWith (P : RProg m d (Λ × Ph)) (oracle : Fin d → List Bool → Bool) (W : ℤ)
    (c : Cfg m Bool (Λ × Ph) x) (b : Bool) : Prop :=
  ∃ T, (rrun P oracle c T).state = none ∧ (rrun P oracle c T).output = c.output ++ [b] ∧
    (∀ r, -1 ≤ (rrun P oracle c T).workTapePos r ∧ (rrun P oracle c T).workTapePos r ≤ W) ∧
    ∀ t < T, Mid P W (rrun P oracle c t)

section Steps

variable (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)

/-- **Simulating `inc r`**: the compiled increment fragment takes the program configuration at `l`
to the one at `l'` with `v r` replaced by `v r + 1`, the register head within `[-1, W]`.

**Proof sketch.** Apply `inc_run` to register `r` holding `bits (v r)`; its end view is the
program configuration at `l'` with `bits (v r + 1)` written (`regCfg_aseam`), and its
intermediate views are register views with the head in range, hence in the middle of a fragment
(`mid_regCfg`). -/
lemma sim_inc (l l' : Λ) (r : Fin m) (hA : A l = .inc r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : ((Nat.bits (v r + 1)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x l' (Function.update v r (v r + 1)) out) := by
  obtain ⟨T, h1, hm⟩ := inc_run (armProg A l₀) oracle r (l, .start) (l, .incB) (l', .start)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r)
  rw [← aseam_eq_regCfg, regCfg_aseam] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨s, f, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [← aseam_eq_regCfg] at hq
  rw [hq]
  exact mid_regCfg A l₀ l v out r s f q W
    (by rcases hs with rfl | rfl <;> (rw [armProg_call, hA]; rfl)) ⟨hq1, hq2.trans hW⟩
    (by omega)

/-- **Simulating `dec r`**: the compiled decrement fragment takes the program configuration at `l`
to the one at `l'` with `v r` replaced by `v r - 1`, the register head within `[-1, W]`.

**Proof sketch.** Apply `dec_run` to register `r` holding `bits (v r)`; its end view is the
program configuration at `l'` with `bits (v r - 1)` written (`regCfg_aseam`), and its
intermediate views are register views with the head in range, hence in the middle of a fragment
(`mid_regCfg`). -/
lemma sim_dec (l l' : Λ) (r : Fin m) (hA : A l = .dec r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x l' (Function.update v r (v r - 1)) out) := by
  obtain ⟨T, h1, hm⟩ := dec_run (armProg A l₀) oracle r (l, .start) (l, .decL) (l, .decE)
    (l, .decB) (l', .start) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r)
  rw [← aseam_eq_regCfg, regCfg_aseam] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨s, f, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [← aseam_eq_regCfg] at hq
  rw [hq]
  exact mid_regCfg A l₀ l v out r s f q W hs ⟨hq1, hq2.trans hW⟩ (by omega)

/-- **Simulating `clr r`**: the compiled clear fragment takes the program configuration at `l` to
the one at `l'` with `v r` replaced by `0`, the register head within `[-1, W]`.

**Proof sketch.** Apply `clr_run` to register `r` holding `bits (v r)`; its end view is the
program configuration at `l'` with the empty word `bits 0` (`regCfg_aseam`), and its
intermediate views are register views with the head in range, hence in the middle of a fragment
(`mid_regCfg`). -/
lemma sim_clr (l l' : Λ) (r : Fin m) (hA : A l = .clr r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' (Function.update v r 0) out) := by
  obtain ⟨T, h1, hm⟩ := clr_run (armProg A l₀) oracle r (l, .start) (l, .clrE) (l', .start)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r)
  rw [← aseam_eq_regCfg, regCfg_aseam] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨s, f, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [← aseam_eq_regCfg] at hq
  rw [hq]
  exact mid_regCfg A l₀ l v out r s f q W hs ⟨hq1, hq2.trans hW⟩ (by omega)

/-- **Simulating `half r`**: the compiled halving fragment takes the program configuration at `l` to
the one at `l'` with `v r` replaced by `v r / 2`, the register head within `[-1, W]`.

**Proof sketch.** Apply `half_run` to register `r` holding `bits (v r)`; its end view is the
program configuration at `l'` with `bits (v r / 2)` written (`regCfg_aseam`), and its
intermediate views are register views with the head in range, hence in the middle of a fragment
(`mid_regCfg`). -/
lemma sim_half (l l' : Λ) (r : Fin m) (hA : A l = .half r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x l' (Function.update v r (v r / 2)) out) := by
  obtain ⟨T, h1, hm⟩ := half_run (armProg A l₀) oracle r (l, .start) (l, .h0) (l, .hF) (l, .hT)
    (l', .start) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r)
  rw [← aseam_eq_regCfg, regCfg_aseam] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨s, f, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [← aseam_eq_regCfg] at hq
  rw [hq]
  exact mid_regCfg A l₀ l v out r s f q W hs ⟨hq1, hq2.trans hW⟩ (by omega)

/-- A one-step control transition between seams. -/
lemma sim_go (l : Λ) (v : Fin m → ℕ) (out : List Bool) (W : ℤ) (hW : 0 ≤ W) (target : Λ)
    (hc : (armProg A l₀).call (l, .start) = none)
    (htr : ∀ a, (armProg A l₀).tm.tr (l, .start) a
      (fun r => FinTM.bufferTape (Nat.bits (v r)) 0) = goAct (target, .start)) :
    SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x target v out) := by
  refine ⟨1, ?_, fun t ht => ?_⟩
  · rw [rrun_one, rstep_noncall _ oracle _ (l, .start) rfl hc]
    unfold MultiTapeTM.step
    have hw : (aseam x l v out).workTapeSymbols = fun r => FinTM.bufferTape (Nat.bits (v r)) 0 := by
      funext r; simp [aseam, Cfg.workTapeSymbols]
    simp only [aseam]
    rw [show (⟨some (l, Ph.start), ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)),
      fun _ => 0, out⟩ : Cfg m Bool (Λ × Ph) x) = aseam x l v out from rfl, hw, htr]
    simp [goAct, Action.apply, aseam]
  · obtain rfl : t = 0 := by omega
    refine ⟨fun s h => ?_, fun r => ?_⟩
    · simp [rrun_zero, aseam] at h; rw [← h]; exact hc
    · simp [rrun_zero, aseam]; omega

/-- **Simulating `jz r`**: one step takes the program configuration at `l` to the one at `l₁` if `v
r = 0` and at `l₀'` otherwise. -/
lemma sim_jz (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jz r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : 0 ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if v r = 0 then l₁ else l₀') v out) := by
  refine sim_go A l₀ oracle l v out W hW _ (by rw [armProg_call, hA]; rfl) (fun a => ?_)
  rw [armProg_tr, hA]
  simp only [insTr]
  congr 2
  have : FinTM.bufferTape (Nat.bits (v r)) 0 = (Nat.bits (v r)).head? := by
    simp [FinTM.bufferTape, List.head?_eq_getElem?]
  simp only [this, bits_head_odd]
  by_cases h : v r = 0 <;> simp [h]

/-- **Simulating `jodd r`**: one step takes the program configuration at `l` to the one at `l₁` if
`v r` is odd and at `l₀'` otherwise. -/
lemma sim_jodd (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jodd r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : 0 ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if v r % 2 = 1 then l₁ else l₀') v out) := by
  refine sim_go A l₀ oracle l v out W hW _ (by rw [armProg_call, hA]; rfl) (fun a => ?_)
  rw [armProg_tr, hA]
  simp only [insTr]
  congr 2
  have : FinTM.bufferTape (Nat.bits (v r)) 0 = (Nat.bits (v r)).head? := by
    simp [FinTM.bufferTape, List.head?_eq_getElem?]
  simp only [this, bits_head_odd]
  by_cases h : v r = 0
  · simp [h]
  · by_cases h' : v r % 2 = 1 <;> simp [h, h']

/-- **Simulating `jeq r s`**: the compiled equality fragment takes the program configuration at `l`
to the one at `l₁` if `v r = v s` and at `l₀'` otherwise, registers unchanged, register heads
within `[-1, W]`.

**Proof sketch.** Unfold the compiled instruction to the two-register comparison fragment and
apply `eq_run` with the binary words of `v r` and `v s` on the two registers; its final view at
the outcome label is the program configuration there (`eqCfg_aseam`), and its intermediate views
are in the middle of a fragment (`Mid`). -/
lemma sim_jeq (l l₁ l₀' : Λ) (r s : Fin m) (hrs : r ≠ s) (hA : A l = .jeq r s l₁ l₀')
    (v : Fin m → ℕ) (out : List Bool) (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if v r = v s then l₁ else l₀') v out) := by
  obtain ⟨T, h1, hm⟩ := eq_run (armProg A l₀) oracle r s hrs (l, .start) (l, .eqBy) (l, .eqBn)
    (l₁, .start) (l₀', .start) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (aseam x l v out) (v r) (v s) rfl rfl
  have e0 : eqCfg (aseam x l v out) (l, .start) r s 0 = aseam x l v out := eqCfg_aseam l l v out r s
  rw [e0] at h1 hm
  have e1 : eqCfg (aseam x l v out) (if v r = v s then (l₁, Ph.start) else (l₀', Ph.start)) r s 0 =
      aseam x (if v r = v s then l₁ else l₀') v out := by
    split_ifs <;> exact eqCfg_aseam _ _ v out r s
  rw [e1] at h1
  refine ⟨T, h1, fun t ht => ?_⟩
  obtain ⟨st, q, hq, hs, hq1, hq2⟩ := hm t ht
  rw [hq]
  refine ⟨fun s' h => ?_, fun r' => ?_⟩
  · simp only [eqCfg, Option.some.injEq] at h; rw [← h]; exact hs
  · simp only [eqCfg, aseam, Function.update_apply]
    split_ifs <;> omega

/-- **Simulating `call`**: one step of the program at a call node takes the program configuration at
`l` to the one at `l₁` if the decider accepts the virtual input built from the input and the
argument registers' words, and at `l₀'` otherwise. -/
lemma sim_call (l l₁ l₀' : Λ) (j : Fin d) (md : Mode) (args : List (Fin m))
    (hA : A l = .call j md args l₁ l₀') (v : Fin m → ℕ) (out : List Bool) :
    rrun (armProg A l₀) oracle (aseam x l v out) 1 =
      aseam x (if oracle j (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r))))
        then l₁ else l₀') v out := by
  rw [rrun_one]
  have hc : (armProg A l₀).call (l, .start) = some ⟨j, md, args, (l₁, .start), (l₀', .start)⟩ := by
    rw [armProg_call, hA]; rfl
  have hw : regWords (aseam x l v out) = fun r => Nat.bits (v r) := by
    funext r; simp [regWords, aseam, tapeWord_bufferTape]
  simp only [rstep, aseam, hc]
  rw [show (⟨some (l, Ph.start), ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)),
      fun _ => 0, out⟩ : Cfg m Bool (Λ × Ph) x) = aseam x l v out from rfl, hw]
  have hseg : callSegs (⟨j, md, args, (l₁, Ph.start), (l₀', Ph.start)⟩ : CallSpec m d (Λ × Ph)) x
      (fun r => Nat.bits (v r)) = callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r)) := rfl
  rw [hseg]
  split_ifs <;> rfl

/-- **Simulating `ret b`**: one step from the program configuration at `l` halts with `b` appended
to the output, the register heads at `0`. -/
lemma sim_ret (l : Λ) (b : Bool) (hA : A l = .ret b) (v : Fin m → ℕ) (out : List Bool) (W : ℤ)
    (hW : 0 ≤ W) : HaltsWith (armProg A l₀) oracle W (aseam x l v out) b := by
  have hc : (armProg A l₀).call (l, .start) = none := by rw [armProg_call, hA]; rfl
  have h1 : rrun (armProg A l₀) oracle (aseam x l v out) 1 =
      ⟨none, ⟨1, by omega⟩, fun r => FinTM.bufferTape (Nat.bits (v r)), fun _ => 0, out ++ [b]⟩ := by
    rw [rrun_one, rstep_noncall _ oracle _ (l, .start) rfl hc]
    unfold MultiTapeTM.step
    simp only [aseam]
    rw [armProg_tr, hA]
    simp [insTr, retAct, Action.apply]
  refine ⟨1, by rw [h1], by rw [h1]; rfl, fun r => by rw [h1]; simp; omega, fun t ht => ?_⟩
  obtain rfl : t = 0 := by omega
  refine ⟨fun s h => ?_, fun r => ?_⟩
  · simp [rrun_zero, aseam] at h; rw [← h]; exact hc
  · simp [rrun_zero, aseam]; omega

/-- A rejecting xCfg run is a halting simulated run. -/
lemma haltsWith_of_rejects (l : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) (W : ℤ)
    (hW : 0 ≤ W) (h : Rejects (armProg A l₀) oracle (aseam x l v out) (aseam x l v out) r 0) :
    HaltsWith (armProg A l₀) oracle W (aseam x l v out) false := by
  obtain ⟨T, e1, e2, e3, hm⟩ := h
  refine ⟨T, e1, e2, fun r' => ?_, fun t ht => ?_⟩
  · rw [e3]; simp only [aseam, Function.update_apply]; split_ifs <;> omega
  · obtain ⟨s, ip, hs, hc⟩ := hm t ht
    rw [hs]; exact mid_xCfg A l₀ l v out r s ip 0 W hc ⟨by omega, hW⟩ hW

/-- A reaching xCfg run is a simulated run. -/
lemma simTo_of_reaches (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) (W : ℤ)
    (hW : 0 ≤ W)
    (h : Reaches (armProg A l₀) oracle (aseam x l v out) (aseam x l' v out) (aseam x l v out) r 0) :
    SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v out) := by
  obtain ⟨T, e1, hm⟩ := h
  refine ⟨T, e1, fun t ht => ?_⟩
  obtain ⟨s, ip, hs, hc⟩ := hm t ht
  rw [hs]; exact mid_xCfg A l₀ l v out r s ip 0 W hc ⟨by omega, hW⟩ hW

/-- A bounded reaching xCfg run is a simulated run. -/
lemma simTo_of_reachesB (l l' : Λ) (v : Fin m → ℕ) (out : List Bool) (r : Fin m) (L W : ℤ)
    (hW : 0 ≤ W) (hL : L ≤ W)
    (h : ReachesB (armProg A l₀) oracle (aseam x l v out) (aseam x l' v out) (aseam x l v out) r L) :
    SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v out) := by
  obtain ⟨T, e1, hm⟩ := h
  refine ⟨T, e1, fun t ht => ?_⟩
  obtain ⟨s, ip, q, hs, hc, hq1, hq2⟩ := hm t ht
  rw [hs]; exact mid_xCfg A l₀ l v out r s ip q W hc ⟨hq1, hq2.trans hL⟩ hW

/-- **Simulating `valP`**: on a well-formed plain input `⟨1ⁿ, w⟩` the compiled plain format check
moves from `l` to `l'` with nothing else changed; otherwise it halts answering `false`.

**Proof sketch.** The compiled check is the plain format-check fragment; `valPlain_run` gives
either a run reaching the rewound start configuration at `l'` (identified with the program
configuration by `xCfg_aseam`) or a rejecting run, turned into the two conclusions by
`simTo_of_reaches` and `haltsWith_of_rejects`. -/
lemma sim_valP (l l' : Λ) (r : Fin m) (hA : A l = .valP r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : 0 ≤ W) :
    (ValidPlain x → SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v out)) ∧
    (¬ ValidPlain x → HaltsWith (armProg A l₀) oracle W (aseam x l v out) false) := by
  have hrun := valPlain_run (armProg A l₀) oracle r (l, .start) (l, .vU1) (l, .vS) (l, .vW0)
    (l, .vWF) (l, .vWT) (l, .vrw1) (l, .vrw2) (l', .start)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl) (aseam x l v out) 0
  obtain ⟨h1, h2⟩ := hrun
  rw [← xCfg_aseam_self] at h1 h2
  rw [xCfg_aseam] at h1
  exact ⟨fun h => simTo_of_reaches A l₀ oracle l l' v out r W hW (h1 h),
    fun h => haltsWith_of_rejects A l₀ oracle l v out r W hW (h2 h)⟩

/-- **Simulating `valQ`**: on a well-formed pair input `⟨1ⁿ, ⟨u, w⟩⟩` the compiled pair format check
moves from `l` to `l'` with nothing else changed; otherwise it halts answering `false`.

**Proof sketch.** The compiled check is the pair format-check fragment; `valPair_run` gives
either a run reaching the rewound start configuration at `l'` (identified with the program
configuration by `xCfg_aseam`) or a rejecting run. Intermediate configurations are
input-scanning views, hence in the middle of a fragment (`mid_xCfg`). -/
lemma sim_valQ (l l' : Λ) (r : Fin m) (hA : A l = .valQ r l') (v : Fin m → ℕ) (out : List Bool)
    (W : ℤ) (hW : 0 ≤ W) :
    (ValidPair x → SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v out)) ∧
    (¬ ValidPair x → HaltsWith (armProg A l₀) oracle W (aseam x l v out) false) := by
  have hrun := valPair_run (armProg A l₀) oracle r (l, .start) (l, .vU1) (l, .vS)
    (fun lst => (l, .vP1 lst)) (fun b lst => (l, .vP2 b lst)) (l, .vW0) (l, .vWF) (l, .vWT)
    (l, .vrw1) (l, .vrw2) (l', .start)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun lst a w => by rw [armProg_tr, hA]; rfl)
    (fun b lst a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (fun lst => by rw [armProg_call, hA]; rfl)
    (fun b lst => by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl) (aseam x l v out) 0
  obtain ⟨h1, h2⟩ := hrun
  rw [← xCfg_aseam_self] at h1 h2
  rw [xCfg_aseam] at h1
  exact ⟨fun h => simTo_of_reaches A l₀ oracle l l' v out r W hW (h1 h),
    fun h => haltsWith_of_rejects A l₀ oracle l v out r W hW (h2 h)⟩

/-- **Simulating `jeqIn r`** on a well-formed plain input `⟨1ⁿ, w⟩`: the compiled comparison moves
from `l` to `l₁` if `bits (v r) = w` and to `l₀'` otherwise, with nothing else changed.

**Proof sketch.** Decompose the input as `⟨1ⁿ, w⟩` and apply `jeqPlain_run` to the register
holding `bits (v r)`; its end view is the program configuration at the outcome label
(`xCfg_aseam`) and `plainWord_pairEncode` identifies `w`. Intermediate configurations are
input-scanning views with the register head in range (`mid_xCfg`). -/
lemma sim_jeqIn (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jeqIn r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) (hx : ValidPlain x) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if Nat.bits (v r) = plainWord x then l₁ else l₀') v out) := by
  obtain ⟨n, w, rfl, -⟩ := hx
  obtain ⟨T, h1, hm⟩ := jeqPlain_run (armProg A l₀) oracle r (l, .start) (l, .jK2) (l, .jC)
    (fun b => (l, .jRB b)) (fun b => (l, .jI1 b)) (fun b => (l, .jI2 b)) (l₁, .start)
    (l₀', .start) (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun b a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl) (fun b a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (fun b => by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (aseam _ l v out) n w rfl (v r) rfl
  rw [← xCfg_aseam_self] at h1 hm
  rw [plainWord_pairEncode]
  have e : (if w = Nat.bits (v r) then ((l₁, Ph.start) : Λ × Ph) else (l₀', Ph.start)) =
      ((if Nat.bits (v r) = w then l₁ else l₀'), Ph.start) := by
    by_cases h : w = Nat.bits (v r)
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e, xCfg_aseam] at h1
  exact simTo_of_reachesB A l₀ oracle l _ v out r _ W (by omega) hW ⟨T, h1, hm⟩

/-- **Simulating `jeqSnd r`** on a well-formed pair input `⟨1ⁿ, ⟨u, w⟩⟩`: the compiled comparison
moves from `l` to `l₁` if `bits (v r) = w` and to `l₀'` otherwise, with nothing else changed.

**Proof sketch.** Decompose the input and apply `jeqPairSnd_run` (skip `1²ⁿ01` and the doubled
`u`, then compare in lockstep). Its end view is the program configuration at the outcome label,
`pairWords_pairEncode` identifies `w`, and the run stays in the middle of a fragment. -/
lemma sim_jeqSnd (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jeqSnd r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) (hx : ValidPair x) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if Nat.bits (v r) = (pairWords x).2 then l₁ else l₀') v out) := by
  obtain ⟨n, u, w, rfl, -, -⟩ := hx
  have h := jeqPairSnd_run (armProg A l₀) oracle r (l, .start) (l, .jK2) (l, .jC)
    (fun b => (l, .jRB b)) (fun b => (l, .jI1 b)) (fun b => (l, .jI2 b)) (l₁, .start)
    (l₀', .start) (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl) (fun b a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (fun b => by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (l, .jP1) (l, .jP2F) (l, .jP2T) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (aseam _ l v out) n u w rfl (v r) rfl
  rw [← xCfg_aseam_self] at h
  rw [pairWords_pairEncode]
  have e : (if w = Nat.bits (v r) then ((l₁, Ph.start) : Λ × Ph) else (l₀', Ph.start)) =
      ((if Nat.bits (v r) = w then l₁ else l₀'), Ph.start) := by
    by_cases h : w = Nat.bits (v r)
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e, xCfg_aseam] at h
  exact simTo_of_reachesB A l₀ oracle l _ v out r _ W (by omega) hW h

/-- **Simulating `jeqFst r`** on a well-formed pair input `⟨1ⁿ, ⟨u, w⟩⟩`: the compiled comparison
moves from `l` to `l₁` if `bits (v r) = u` and to `l₀'` otherwise, with nothing else changed.

**Proof sketch.** Decompose the input and apply `jeqPairFst_run` (skip `1²ⁿ01`, then compare the
register with the doubled `u` in lockstep). Its end view is the program configuration at the
outcome label, `pairWords_pairEncode` identifies `u`, and the run stays in the middle of a
fragment. -/
lemma sim_jeqFst (l l₁ l₀' : Λ) (r : Fin m) (hA : A l = .jeqFst r l₁ l₀') (v : Fin m → ℕ)
    (out : List Bool) (W : ℤ) (hW : ((Nat.bits (v r)).length : ℤ) ≤ W) (hx : ValidPair x) :
    SimTo (armProg A l₀) oracle W (aseam x l v out)
      (aseam x (if Nat.bits (v r) = (pairWords x).1 then l₁ else l₀') v out) := by
  obtain ⟨n, u, w, rfl, -, -⟩ := hx
  have h := jeqPairFst_run (armProg A l₀) oracle r (l, .start) (l, .jK2)
    (fun b => (l, .jRB b)) (fun b => (l, .jI1 b)) (fun b => (l, .jI2 b)) (l₁, .start)
    (l₀', .start) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl) (fun b a w => by rw [armProg_tr, hA]; rfl)
    (fun b a w => by rw [armProg_tr, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (fun b => by rw [armProg_call, hA]; rfl)
    (fun b => by rw [armProg_call, hA]; rfl) (fun b => by rw [armProg_call, hA]; rfl)
    (l, .jD1) (l, .jD2F) (l, .jD2T) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (fun a w => by rw [armProg_tr, hA]; rfl)
    (fun a w => by rw [armProg_tr, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (by rw [armProg_call, hA]; rfl) (by rw [armProg_call, hA]; rfl)
    (aseam _ l v out) n u w rfl (v r) rfl
  rw [← xCfg_aseam_self] at h
  rw [pairWords_pairEncode]
  have e : (if u = Nat.bits (v r) then ((l₁, Ph.start) : Λ × Ph) else (l₀', Ph.start)) =
      ((if Nat.bits (v r) = u then l₁ else l₀'), Ph.start) := by
    by_cases h : u = Nat.bits (v r)
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e, xCfg_aseam] at h
  exact simTo_of_reachesB A l₀ oracle l _ v out r _ W (by omega) hW h

end Steps

end Complexity.LogProg
