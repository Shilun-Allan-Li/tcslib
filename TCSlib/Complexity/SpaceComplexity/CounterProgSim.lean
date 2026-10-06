/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.TuringMachine.CounterProgRun
import TCSlib.Complexity.SpaceComplexity.UnaryLogspace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulating counter programs in logarithmic space

A counter program (`Complexity.CounterProg`, the model of the emitters of [AB09, Remark 6.7])
that runs for polynomially many steps keeps every register polynomially bounded, so its
registers fit in `O(log n)` bits. This file builds the abstract register machine
`Complexity.CPSim.A P l₀ lm` that, on `⟨1ⁿ, bits p⟩`, runs `P` with its registers, its input
position and the *number* of printed bits held in binary, reading the input of `P` through
two deciders (the length and bit languages of the input) and stopping at the `p`-th printed
bit [AB09, §4.3: composing implicitly logspace computable functions, by recomputing bits on
demand].

This file defines the machine and proves the simulation of one counter step
(`Complexity.CPSim.sim_step`); the whole run and the resulting closure property are in
`TCSlib.Complexity.SpaceComplexity.CounterProgSimRun`.

## Main definitions

* `Complexity.CPSim.A` — the simulating machine; `lm` selects the length language.
* `Complexity.CPSim.ev` — the register file of a counter state.

## Main results

* `Complexity.CPSim.sim_step` — one counter step is simulated, or the machine answers.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Lemma 4.17; §6.1.1, Remark 6.7.)
-/

namespace Complexity

namespace CPSim

open Turing LogProg

variable {R : ℕ} {Λ : Type}

/-! ## The register file -/

/-- The register of counter register `r`. -/
def rg (r : Fin R) : Fin (R + 3) := Fin.castAdd 3 r
/-- The register of the input position. -/
def rP (R : ℕ) : Fin (R + 3) := ⟨R, by omega⟩
/-- The register of the number of printed bits. -/
def rO (R : ℕ) : Fin (R + 3) := ⟨R + 1, by omega⟩
/-- The scratch register of the print loop. -/
def rT (R : ℕ) : Fin (R + 3) := ⟨R + 2, by omega⟩

/-- The register file: counter registers `ρ`, input position `p`, output count `oc`, scratch
`tm`. -/
def ev (ρ : Fin R → ℕ) (p oc tm : ℕ) : Fin (R + 3) → ℕ := fun i =>
  if h : i.val < R then ρ ⟨i.val, h⟩ else if i.val = R then p else if i.val = R + 1 then oc
  else tm

/-- Reading a counter register. -/
@[simp] lemma ev_rg (ρ : Fin R → ℕ) (p oc tm : ℕ) (r : Fin R) : ev ρ p oc tm (rg r) = ρ r := by
  simp [ev, rg]
/-- Reading the input position. -/
@[simp] lemma ev_rP (ρ : Fin R → ℕ) (p oc tm : ℕ) : ev ρ p oc tm (rP R) = p := by simp [ev, rP]
/-- Reading the output count. -/
@[simp] lemma ev_rO (ρ : Fin R → ℕ) (p oc tm : ℕ) : ev ρ p oc tm (rO R) = oc := by
  simp [ev, rO]
/-- Reading the scratch register. -/
@[simp] lemma ev_rT (ρ : Fin R → ℕ) (p oc tm : ℕ) : ev ρ p oc tm (rT R) = tm := by
  simp [ev, rT]

/-- Writing a counter register. -/
lemma upd_rg (ρ : Fin R → ℕ) (p oc tm : ℕ) (r : Fin R) (v : ℕ) :
    Function.update (ev ρ p oc tm) (rg r) v = ev (Function.update ρ r v) p oc tm := by
  funext i
  obtain ⟨i, hi⟩ := i
  obtain ⟨r, hr⟩ := r
  simp only [Function.update_apply, ev, rg, Fin.ext_iff, Fin.coe_castAdd]
  split_ifs <;> simp_all

/-- Writing the input position. -/
lemma upd_rP (ρ : Fin R → ℕ) (p oc tm v : ℕ) :
    Function.update (ev ρ p oc tm) (rP R) v = ev ρ v oc tm := by
  funext i; obtain ⟨i, hi⟩ := i
  simp only [Function.update_apply, ev, rP, Fin.ext_iff]
  split_ifs <;> omega

/-- Writing the output count. -/
lemma upd_rO (ρ : Fin R → ℕ) (p oc tm v : ℕ) :
    Function.update (ev ρ p oc tm) (rO R) v = ev ρ p v tm := by
  funext i; obtain ⟨i, hi⟩ := i
  simp only [Function.update_apply, ev, rO, Fin.ext_iff]
  split_ifs <;> omega

/-- Writing the scratch register. -/
lemma upd_rT (ρ : Fin R → ℕ) (p oc tm v : ℕ) :
    Function.update (ev ρ p oc tm) (rT R) v = ev ρ p oc v := by
  funext i; obtain ⟨i, hi⟩ := i
  simp only [Function.update_apply, ev, rT, Fin.ext_iff]
  split_ifs <;> omega

/-- The scratch register is not a counter register. -/
lemma rT_ne_rg (r : Fin R) : rT R ≠ rg r := by
  intro h; have := congrArg Fin.val h; simp [rT, rg] at this; omega

/-! ## The machine -/

/-- The labels: simulating label `l`, and the auxiliary labels of the output count, the print
loop and the input read. -/
inductive Lb (Λ : Type) where
  | start
  | sim (l : Λ)
  | bump (l : Λ)
  | prL (l : Λ)
  | prC (l : Λ)
  | prB (l : Λ)
  | prT (l : Λ)
  | rdB (l : Λ)
  | rdT (l : Λ)
  | rdF (l : Λ)
  | ans (b : Bool)
  deriving DecidableEq

/-- Finitely many labels (via an explicit equivalence with `(Unit ⊕ Fin 9 × Λ) ⊕ Bool`). -/
instance [Fintype Λ] : Fintype (Lb Λ) := by
  classical
  let e : Lb Λ ≃ (Unit ⊕ (Fin 9 × Λ)) ⊕ Bool :=
    { toFun := fun q => match q with
        | .start => .inl (.inl ())
        | .sim l => .inl (.inr (0, l))
        | .bump l => .inl (.inr (1, l))
        | .prL l => .inl (.inr (2, l))
        | .prC l => .inl (.inr (3, l))
        | .prB l => .inl (.inr (4, l))
        | .prT l => .inl (.inr (5, l))
        | .rdB l => .inl (.inr (6, l))
        | .rdT l => .inl (.inr (7, l))
        | .rdF l => .inl (.inr (8, l))
        | .ans b => .inr b
      invFun := fun z => match z with
        | .inl (.inl ()) => .start
        | .inl (.inr (i, l)) =>
          match i with
          | 0 => .sim l | 1 => .bump l | 2 => .prL l | 3 => .prC l | 4 => .prB l
          | 5 => .prT l | 6 => .rdB l | 7 => .rdT l | 8 => .rdF l
        | .inr b => .ans b
      left_inv := fun q => by cases q <;> rfl
      right_inv := fun z => by
        rcases z with (⟨⟩ | ⟨i, l⟩) | b
        · rfl
        · fin_cases i <;> rfl
        · rfl }
  exact Fintype.ofEquiv _ e.symm

variable (P : Λ → CounterProg.Instr R Λ) (l₀ : Λ) (lm : Bool)

/-- **The simulating machine.** At `sim l` it executes `P l`: register instructions act on the
corresponding registers; printing a bit compares the output count with the index `p` on the
input (answer if equal, else count); printing a register loops over the scratch register;
reading asks the length decider (`0`) and the bit decider (`1`) about the input position;
`halt` answers `0` (the index is beyond the output). In length mode (`lm`) every printed bit
answers `1`. -/
def A : ARM (R + 3) 2 (Lb Λ) := fun q =>
  match q with
  | .start => .valP (rP R) (.sim l₀)
  | .sim l =>
    match P l with
    | .halt => .ret false
    | .goto l' => .jz (rP R) (.sim l') (.sim l')
    | .out b l' => .jeqIn (rO R) (.ans (lm || b)) (.bump l')
    | .inc r l' => .inc (rg r) (.sim l')
    | .dec r l' => .dec (rg r) (.sim l')
    | .jz r l0 l1 => .jz (rg r) (.sim l0) (.sim l1)
    | .pr _ _ => .clr (rT R) (.prL l)
    | .rd le _ _ => .call 0 .unaryFst [rP R] (.rdB l) (.sim le)
  | .bump l' => .inc (rO R) (.sim l')
  | .prL l =>
    match P l with
    | .pr r l' => .jeq (rT R) (rg r) (.sim l') (.prC l)
    | _ => .ret false
  | .prC l => .jeqIn (rO R) (.ans true) (.prB l)
  | .prB l => .inc (rO R) (.prT l)
  | .prT l => .inc (rT R) (.prL l)
  | .rdB l => .call 1 .unaryFst [rP R] (.rdT l) (.rdF l)
  | .rdT l =>
    match P l with
    | .rd _ _ lt => .inc (rP R) (.sim lt)
    | _ => .ret false
  | .rdF l =>
    match P l with
    | .rd _ lf _ => .inc (rP R) (.sim lf)
    | _ => .ret false
  | .ans b => .ret b

/-- On a well-formed input every configuration meets the syntactic preconditions. -/
lemma preS_A {y : List Bool} (hv : ValidPlain y) (a : AConf (R + 3) (Lb Λ)) :
    PreS (A P l₀ lm) y a := by
  obtain ⟨_ | q, v, res⟩ := a
  · trivial
  · cases q with
    | sim l => cases h : P l <;> simp [PreS, A, h, hv]
    | prL l => cases h : P l <;> simp [PreS, A, h, rT_ne_rg]
    | rdT l => cases h : P l <;> simp [PreS, A, h]
    | rdF l => cases h : P l <;> simp [PreS, A, h]
    | _ => simp [PreS, A, hv]

/-! ## One step -/

/-- The answer for index `p` on output `O`: the bit `O_p`, or in length mode `p < |O|`. -/
def ans (lm : Bool) (O : List Bool) (p : ℕ) : Bool :=
  if lm then decide (p < O.length) else O.getD p false

/-- A running abstract configuration. -/
abbrev cf (q : Lb Λ) (v : Fin (R + 3) → ℕ) : AConf (R + 3) (Lb Λ) := (some q, v, none)

section Step

variable {n p : ℕ} {u : List Bool} {o : Fin 2 → List Bool → Bool}
  (ho0 : ∀ h, o 0 (pairEncode (List.replicate n true) (Nat.bits h)) = decide (h < u.length))
  (ho1 : ∀ h, o 1 (pairEncode (List.replicate n true) (Nat.bits h)) = u.getD h false)
  (B : ℕ)

/-- The invariant of the simulation: preconditions, and registers at most `B`. -/
def G (y : List Bool) (a : AConf (R + 3) (Lb Λ)) : Prop :=
  PreS (A P l₀ lm) y a ∧ ∀ r, a.2.1 r ≤ B

variable {P l₀ lm B}

/-- Configurations with all values within `B` satisfy the invariant. -/
lemma G_ev (q : Lb Λ) (ρ : Fin R → ℕ) (ps oc tm : ℕ) (hρ : ∀ r, ρ r ≤ B) (hps : ps ≤ B)
    (hoc : oc ≤ B) (htm : tm ≤ B) :
    G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)) (cf q (ev ρ ps oc tm)) := by
  refine ⟨preS_A P l₀ lm ⟨n, _, rfl, canon_bits p⟩ _, fun i => ?_⟩
  obtain ⟨i, hi⟩ := i
  simp only [ev]
  split_ifs
  · exact hρ _
  all_goals assumption

/-- The output-count comparison: `bits oc = bits p` iff `oc = p`. -/
lemma jeqIn_eq (oc : ℕ) :
    (Nat.bits oc = plainWord (pairEncode (List.replicate n true) (Nat.bits p))) ↔ oc = p := by
  rw [plainWord_pairEncode, bits_injective.eq_iff]

/-- **The print loop**, when the whole value fits below the index: from `prL` with scratch
`j` and count `o₀ + j` the machine reaches the next label with count `o₀ + V`.

**Proof sketch.** Induction on the remaining count `d`: each round goes through `prL` (scratch
`≠` value), `prC` (count `≠ p`), `prB` (count `+1`) and `prT` (scratch `+1`); at `d = 0` the
test at `prL` exits to `sim l'`. -/
lemma pr_reach {l l' : Λ} {r : Fin R} (hP : P l = .pr r l') (ρ : Fin R → ℕ) (ps o₀ : ℕ)
    (hρ : ∀ r, ρ r ≤ B) (hps : ps ≤ B) (hle : o₀ + ρ r ≤ p) (hB : o₀ + ρ r ≤ B) :
    ∀ d j, j + d = ρ r →
      AReach (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) (cf (.sim l') (ev ρ ps (o₀ + ρ r) (ρ r))) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    simp only [Nat.add_zero] at hj; subst hj
    refine AReach.step (G_ev _ _ _ _ _ hρ hps (by omega) (by omega)) ?_
    have : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prL l) (ev ρ ps (o₀ + ρ r) (ρ r))) = cf (.sim l') (ev ρ ps (o₀ + ρ r) (ρ r)) := by
      simp [astep, A, hP]
    rw [this]; exact AReach.refl _
  | succ d ih =>
    intro j hj
    have hG := fun q (oc tm : ℕ) (h1 : oc ≤ B) (h2 : tm ≤ B) => G_ev (n := n) (p := p) (P := P)
      (l₀ := l₀) (lm := lm) q ρ ps oc tm hρ hps h1 h2
    refine AReach.step (hG _ _ _ (by omega) (by omega)) ?_
    have e1 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) = cf (.prC l) (ev ρ ps (o₀ + j) j) := by
      simp [astep, A, hP, show j ≠ ρ r by omega]
    rw [e1]
    refine AReach.step (hG _ _ _ (by omega) (by omega)) ?_
    have e2 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prC l) (ev ρ ps (o₀ + j) j)) = cf (.prB l) (ev ρ ps (o₀ + j) j) := by
      simp only [astep, A, ev_rO, jeqIn_eq, show o₀ + j ≠ p by omega, ↓reduceIte]
    rw [e2]
    refine AReach.step (hG _ _ _ (by omega) (by omega)) ?_
    simp only [astep, A, ev_rO, upd_rO]
    refine AReach.step (hG _ _ _ (by omega) (by omega)) ?_
    simp only [astep, A, ev_rT, upd_rT]
    have := ih (j + 1) (by omega)
    rwa [show o₀ + j + 1 = o₀ + (j + 1) by ring]

/-- **The print loop**, when the index falls inside the printed block: the machine answers
`1` when the count reaches the index.

**Proof sketch.** Induction on the distance `d` from the count to `p`: each round goes through
`prL`, `prC`, `prB`, `prT`; at `d = 0` the comparison at `prC` succeeds and the machine
answers `1`. -/
lemma pr_halt {l l' : Λ} {r : Fin R} (hP : P l = .pr r l') (ρ : Fin R → ℕ) (ps o₀ : ℕ)
    (hρ : ∀ r, ρ r ≤ B) (hps : ps ≤ B) (hlt : p < o₀ + ρ r) (hB : o₀ + ρ r ≤ B) :
    ∀ d j, o₀ + j + d = p →
      AHalt (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) true := by
  have hG := fun q (oc tm : ℕ) (h1 : oc ≤ B) (h2 : tm ≤ B) => G_ev (n := n) (p := p) (P := P)
    (l₀ := l₀) (lm := lm) q ρ ps oc tm hρ hps h1 h2
  intro d
  induction d with
  | zero =>
    intro j hj
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    have e1 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) = cf (.prC l) (ev ρ ps (o₀ + j) j) := by
      simp [astep, A, hP, show j ≠ ρ r by omega]
    rw [e1]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    have e2 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prC l) (ev ρ ps (o₀ + j) j)) = cf (.ans true) (ev ρ ps (o₀ + j) j) := by
      simp only [astep, A, ev_rO, jeqIn_eq, show o₀ + j = p by omega, ↓reduceIte]
    rw [e2]
    exact AHalt.ret rfl (hG _ _ _ (by omega) (by omega))
  | succ d ih =>
    intro j hj
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    have e1 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prL l) (ev ρ ps (o₀ + j) j)) = cf (.prC l) (ev ρ ps (o₀ + j) j) := by
      simp [astep, A, hP, show j ≠ ρ r by omega]
    rw [e1]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    have e2 : astep (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (cf (.prC l) (ev ρ ps (o₀ + j) j)) = cf (.prB l) (ev ρ ps (o₀ + j) j) := by
      simp only [astep, A, ev_rO, jeqIn_eq, show o₀ + j ≠ p by omega, ↓reduceIte]
    rw [e2]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    simp only [astep, A, ev_rO, upd_rO]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    simp only [astep, A, ev_rT, upd_rT]
    have := ih (j + 1) (by omega)
    rwa [show o₀ + j + 1 = o₀ + (j + 1) by ring]

include ho0 ho1 in
/-- **One counter step.** From the configuration simulating the counter state
`⟨l, ρ, ps, out⟩` (with `|out| ≤ p`) the machine either answers `0` because `P` halts, or
reaches the configuration simulating the next state, or — if the step prints the `p`-th bit —
answers `ans lm s' p` for the next state `s'`; all through configurations within `B`.

**Proof sketch.** By cases on the instruction: register instructions are one machine step;
printing a bit compares the count with `p` (`jeqIn`); printing a register is the print loop
(`pr_reach`, `pr_halt`); reading asks the length decider, then the bit decider, and advances
the position. -/
lemma sim_step (l : Λ) (ρ : Fin R → ℕ) (ps : ℕ) (out : List Bool) (tm : ℕ)
    (hp : out.length ≤ p) (hρ : ∀ r, ρ r ≤ B) (hps : ps ≤ B) (hout : out.length ≤ B)
    (htm : tm ≤ B) (s' : CounterProg.St R Λ)
    (hs : s' = CounterProg.step P u ⟨some l, ρ, ps, out⟩) (hρ' : ∀ r, s'.regs r ≤ B)
    (hps' : s'.pos ≤ B) (hout' : s'.out.length ≤ B) :
    (s'.lbl = none ∧ s'.out = out ∧
      AHalt (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
        (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
        (cf (.sim l) (ev ρ ps out.length tm)) false) ∨
    (∃ l', s'.lbl = some l' ∧
      ((s'.out.length ≤ p ∧ ∃ tm' ≤ B,
        AReach (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
          (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
          (cf (.sim l) (ev ρ ps out.length tm))
          (cf (.sim l') (ev s'.regs s'.pos s'.out.length tm')))
      ∨ (p < s'.out.length ∧
        AHalt (A P l₀ lm) o (pairEncode (List.replicate n true) (Nat.bits p))
          (G P l₀ lm B (pairEncode (List.replicate n true) (Nat.bits p)))
          (cf (.sim l) (ev ρ ps out.length tm)) (ans lm s'.out p)))) := by
  set y := pairEncode (List.replicate n true) (Nat.bits p) with hy
  have hG0 := G_ev (n := n) (p := p) (P := P) (l₀ := l₀) (lm := lm) (.sim l) ρ ps out.length tm
    hρ hps hout htm
  cases hP : P l with
  | halt =>
    left
    have : s' = ⟨none, ρ, ps, out⟩ := by rw [hs]; simp [CounterProg.step, hP]
    subst this
    exact ⟨rfl, rfl, AHalt.ret (by simp [A, hP]) hG0⟩
  | goto l' =>
    have : s' = ⟨some l', ρ, ps, out⟩ := by rw [hs]; simp [CounterProg.step, hP]
    subst this
    refine Or.inr ⟨l', rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
    have : astep (A P l₀ lm) o y (cf (.sim l) (ev ρ ps out.length tm)) =
        cf (.sim l') (ev ρ ps out.length tm) := by simp [astep, A, hP]
    rw [this]; exact AReach.refl _
  | out b l' =>
    have : s' = ⟨some l', ρ, ps, out ++ [b]⟩ := by rw [hs]; simp [CounterProg.step, hP]
    subst this
    simp only [List.length_append, List.length_singleton] at hout' ⊢
    refine Or.inr ⟨l', rfl, ?_⟩
    by_cases heq : out.length = p
    · refine Or.inr ⟨by omega, AHalt.step hG0 ?_⟩
      have : astep (A P l₀ lm) o y (cf (.sim l) (ev ρ ps out.length tm)) =
          cf (.ans (lm || b)) (ev ρ ps out.length tm) := by
        simp only [astep, A, hP, ev_rO, hy, jeqIn_eq, heq, ↓reduceIte]
      rw [this]
      have ha : ans lm (out ++ [b]) p = (lm || b) := by
        subst heq; cases lm <;> simp [ans, List.getD_eq_getElem?_getD]
      rw [ha]
      exact AHalt.ret rfl (G_ev _ _ _ _ _ hρ hps hout htm)
    · refine Or.inl ⟨by omega, tm, htm, AReach.step hG0 ?_⟩
      have : astep (A P l₀ lm) o y (cf (.sim l) (ev ρ ps out.length tm)) =
          cf (.bump l') (ev ρ ps out.length tm) := by
        simp only [astep, A, hP, ev_rO, hy, jeqIn_eq, heq, ↓reduceIte]
      rw [this]
      refine AReach.step (G_ev _ _ _ _ _ hρ hps hout htm) ?_
      simp only [astep, A, ev_rO, upd_rO]
      exact AReach.refl _
  | inc r l' =>
    have : s' = ⟨some l', Function.update ρ r (ρ r + 1), ps, out⟩ := by
      rw [hs]; simp [CounterProg.step, hP]
    subst this
    refine Or.inr ⟨l', rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
    simp only [astep, A, hP, ev_rg, upd_rg]
    exact AReach.refl _
  | dec r l' =>
    have : s' = ⟨some l', Function.update ρ r (ρ r - 1), ps, out⟩ := by
      rw [hs]; simp [CounterProg.step, hP]
    subst this
    refine Or.inr ⟨l', rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
    simp only [astep, A, hP, ev_rg, upd_rg]
    exact AReach.refl _
  | jz r l0 l1 =>
    have : s' = ⟨some (if ρ r = 0 then l0 else l1), ρ, ps, out⟩ := by
      rw [hs]; simp [CounterProg.step, hP]
    subst this
    refine Or.inr ⟨_, rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
    by_cases hr : ρ r = 0
    · simp only [astep, A, hP, ev_rg, hr, ↓reduceIte]; exact AReach.refl _
    · simp only [astep, A, hP, ev_rg, hr, ↓reduceIte]; exact AReach.refl _
  | pr r l' =>
    have : s' = ⟨some l', ρ, ps, out ++ List.replicate (ρ r) true⟩ := by
      rw [hs]; simp [CounterProg.step, hP]
    subst this
    simp only [List.length_append, List.length_replicate] at hout' ⊢
    refine Or.inr ⟨l', rfl, ?_⟩
    have e0 : astep (A P l₀ lm) o y (cf (.sim l) (ev ρ ps out.length tm)) =
        cf (.prL l) (ev ρ ps (out.length + 0) 0) := by
      simp only [astep, A, hP, upd_rT, Nat.add_zero]
    by_cases hle : out.length + ρ r ≤ p
    · refine Or.inl ⟨hle, ρ r, hρ r, AReach.step hG0 ?_⟩
      rw [e0]
      exact pr_reach hP ρ ps out.length hρ hps hle hout' (ρ r) 0 (by omega)
    · refine Or.inr ⟨by omega, AHalt.step hG0 ?_⟩
      rw [e0]
      have ha : ans lm (out ++ List.replicate (ρ r) true) p = true := by
        cases lm
        · simp only [ans, Bool.false_eq_true, ↓reduceIte, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
          rw [if_pos (by omega)]; rfl
        · simp [ans]; omega
      rw [ha]
      exact pr_halt hP ρ ps out.length hρ hps (by omega) hout' (p - out.length) 0 (by omega)
  | rd le lf lt =>
    have hcall : A P l₀ lm (.sim l) = .call 0 .unaryFst [rP R] (.rdB l) (.sim le) := by
      simp [A, hP]
    cases hx : u[ps]? with
    | none =>
      have : s' = ⟨some le, ρ, ps, out⟩ := by rw [hs]; simp [CounterProg.step, hP, hx]
      subst this
      refine Or.inr ⟨le, rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
      rw [astep_call₁ _ _ hcall, ho0]
      have : ¬ ps < u.length := by
        intro h; rw [List.getElem?_eq_getElem h] at hx; exact absurd hx (by simp)
      simp only [ev_rP, this, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact AReach.refl _
    | some b =>
      have hlt : ps < u.length := (List.getElem?_eq_some_iff.mp hx).1
      have hb : u.getD ps false = b := by simp [List.getD_eq_getElem?_getD, hx]
      have : s' = ⟨some (if b then lt else lf), ρ, ps + 1, out⟩ := by
        rw [hs]; cases b <;> simp [CounterProg.step, hP, hx]
      subst this
      refine Or.inr ⟨_, rfl, Or.inl ⟨hp, tm, htm, AReach.step hG0 ?_⟩⟩
      rw [astep_call₁ _ _ hcall, ho0]
      simp only [ev_rP, hlt, decide_true, ↓reduceIte]
      refine AReach.step (G_ev _ _ _ _ _ hρ hps hout htm) ?_
      rw [astep_call₁ _ _ (show A P l₀ lm (.rdB l) = .call 1 .unaryFst [rP R] (.rdT l) (.rdF l)
        from rfl), ho1]
      simp only [ev_rP, hb]
      refine AReach.step (G_ev _ _ _ _ _ hρ hps hout htm) ?_
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, astep, A, hP, ev_rP, upd_rP]
        exact AReach.refl _
      · simp only [↓reduceIte, astep, A, hP, ev_rP, upd_rP]
        exact AReach.refl _

end Step

end CPSim

end Complexity
