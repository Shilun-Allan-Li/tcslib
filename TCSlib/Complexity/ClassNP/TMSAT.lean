/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.TuringMachine.Universal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# TMSAT: the first NP-complete language

[AB09, Theorem 2.9]: the language
`TMSAT = {⟨α, x, 1^n, 1^t⟩ : ∃ u ∈ {0,1}^n, M_α outputs 1 on ⟨x, u⟩ within t
steps}` is `NP`-complete — the "generic" `NP`-complete problem, read off the
definition of `NP` itself. This module defines `TMSAT` over the audited
Chapter-1 machine-code layer and states Theorem 2.9, together with the
polynomial time-constructibility statement the hardness reduction's unary
components rely on.

## Design and deviations from [AB09]

* **The tuple is right-nested `Turing.pairEncode`**:
  `⟨α, x, 1^n, 1^t⟩` is rendered
  `pairEncode α (pairEncode x (pairEncode 1^n 1^t))`, with `1^k` the string
  `List.replicate k true`. The pairing is self-delimiting and injective
  (`Turing.pairEncode_injective`), so the four components are recoverable and
  unique — strings not of this shape are simply not members.
* **"`M_α` outputs `1` on input `⟨x, u⟩` within `t` steps"** is rendered
  `(c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t` — completed
  output exactly `[true]` by step `t` (halting is absorbing), the audited
  output-convention of the whole development, against the total decoding of a
  `Turing.MachineCode`. The unary components make `n` and `t` at most the
  input length — [AB09]'s footnote 2: padding the input is what entitles the
  verifier and the reduction to run in time polynomial in `n` and `t`.
* **The generality split refines the audited `HALT` treatment**
  (`Complexity.HALT_NPHard` at `Turing.MachineCode`,
  `Complexity.HALT_not_mem_NP` at `Turing.EffectiveMachineCode`): the language
  and its `NP`-hardness need only a lawful code (`decode` totality and
  `decode_encode`; the reduction writes a *fixed* code string), while
  membership in `NP` runs the universal machine over an input-supplied `α` and
  therefore takes an effective scheme **with a polynomially bounded canonizer**
  — the hypothesis `Complexity.PolyBound c.canonizerTime` on the membership
  and completeness statements. Effectivity alone is **not** enough (round-1
  audit, finding 1, Argument A): `Turing.EffectiveMachineCode` bounds the
  canonizer's computability, not its cost, and a lawful effective scheme can
  plant arbitrarily expensive decidable information behind short codes,
  pushing its `TMSAT` outside `EXP ⊇ NP`. `NP`-completeness carries the same
  hypothesis.
* **`Complexity.timeConstructible_poly` is a new statement about a Chapter-1
  notion** (`Complexity.TimeConstructible`, `ClassP/TimeConstructible.lean`) —
  stated here rather than by editing the frozen audited file, and **flagged for
  this phase's audit** exactly as `Complexity.compl_mem_P` was in phase 1. The
  exponent is `c + 1` because time-constructibility requires `T n ≥ n`, which
  degree `0` would violate.

## Main definitions

* `Complexity.TMSAT` — [AB09, Theorem 2.9's language].

## Main results

* `Complexity.timeConstructible_poly` — `n ↦ C·(n+1)^(c+1)` is
  time-constructible (`C > 0`); the plan's supporting obligation for the
  reduction's unary components. [AB09, §1.3]
* `Complexity.timed_universal_quantitative` — the phase-3-mandated new public
  bridge with an explicit code-length coefficient; its proof is escalated
  under the epoch-2 brief's private-API protocol.
* `Complexity.TMSAT_mem_NP` — for schemes with polynomially bounded
  canonizers, the certificate is `u` itself; verification is timed universal
  simulation. [AB09, Theorem 2.9]
* `Complexity.TMSAT_NPHard` — the generic reduction: send `x` to
  `⟨⌞M⌟, x, 1^{p(|x|)}, 1^{q(m)}⟩`. [AB09, Theorem 2.9]
* `Complexity.TMSAT_NPComplete` — [AB09, Theorem 2.9], under the same
  polynomial-canonizer hypothesis as membership.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Theorem 2.9 with footnote 2, pp. 43-44;
  §1.3 for time constructibility.)
-/

namespace Complexity

open Turing

/-- **The language `TMSAT`** [AB09, Theorem 2.9]: quadruples
`⟨α, x, 1^n, 1^t⟩` — right-nested `Turing.pairEncode`, unary third and fourth
components — such that some certificate `u` of length exactly `n` makes the
machine denoted by `α` (total decoding of the scheme `c`) halt on the paired
input `⟨x, u⟩` within `t` steps with completed output exactly `[true]`. -/
def TMSAT (c : MachineCode) : Language Bool :=
  {y | ∃ (α x u : List Bool) (n t : ℕ),
    y = pairEncode α
          (pairEncode x (pairEncode (List.replicate n true) (List.replicate t true))) ∧
    u.length = n ∧
    (c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t}

/-! ### Exact unary polynomial generation

The following private machine enumerates a fixed-dimensional box of side
`|x| + 1`. Its output is a unary polynomial, so composing it with the public
linear-time binary length counter gives an exact binary polynomial value.
No private declaration from the Chapter-1 counter is used.
-/

/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive PolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance polyControlFintype (c C : ℕ) : Fintype (PolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance polyControlDecidableEq (c C : ℕ) : DecidableEq (PolyControl c C) :=
  (proxy_equiv% (PolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def polyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def polyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : PolyControl c C) : Action (c + 1) Bool (PolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def polyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := PolyControl c C
  tm := {
    q₀ := .copy
    tr := fun s inp w => match s with
      | .copy => match inp with
        | some _ => ⟨.pos, fun _ => (some (some true), .pos), none, some .copy⟩
        | none => ⟨0, fun _ => (some (some true), .neg), none, some .setup⟩
      | .setup =>
        if w 0 = none then
          ⟨0, fun _ => (none, .pos), none, some (.loop (Fin.last c))⟩
        else ⟨0, fun _ => (none, .neg), none, some .setup⟩
      | .loop i =>
        if w i = none then polyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then polyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else polyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then polyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def polyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : PolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (PolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => polyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma polyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : PolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (polyMove i d s').apply (polyCfg x q s h o) =
      polyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [polyMove, polyCfg, Action.apply, hj]
  · simp [polyMove, polyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma poly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      polyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        polyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma poly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      polyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (PolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, polyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, polyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [polyCfg] using polyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        polyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (PolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, polyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, polyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [polyCfg, sub_eq_add_neg] using polyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma poly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (polyUnaryTM c C).tm.step
      (polyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      polyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, polyUnaryTM, polyCfg, i.isLt, ↓reduceDIte]
  simpa [polyCfg] using polyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def polyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (polyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma poly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (polyCost q C i + 2) + q + 2) =
      polyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (polyUnaryTM c C).tm.runFrom
          (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (polyCost q C i + 2) =
        polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (polyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', polyCfg, Cfg.workTapeSymbols, polyTape, hj]
      have hs : (polyUnaryTM c C).tm.step (polyCfg x q (.loop ⟨i, hi⟩) h' o) =
          polyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((polyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [polyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [polyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop 0) h' o) _ = _
        rw [show polyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [polyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop 0) h' o) 1 =
            polyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          poly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using poly_advance (C := C) x q h'
          (o ++ List.replicate C true) (⟨0, hi⟩ : Fin (c + 1))
      · have hlow : ∀ k : Fin (c + 1), k.val ≤ i - 1 → h' k = 0 := by
          intro k hk
          have hne : k ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
          simp only [h', Function.update_of_ne hne]
          exact hh k (by omega)
        have hinner := ih (i - 1) (by omega) (by omega) h' hlow o q 0 (by omega)
        have hupdate : Function.update h' ⟨i - 1, by omega⟩ 0 = h' := by
          rw [← hlow ⟨i - 1, by omega⟩ (le_refl _)]
          exact Function.update_eq_self _ _
        have hi' : i - 1 + 1 = i := by omega
        have hout : q * (C * q ^ (i - 1)) = C * q ^ i := by
          calc
            q * (C * q ^ (i - 1)) = C * (q ^ (i - 1) * q) := by ring
            _ = C * q ^ i := by simp only [← Nat.pow_succ, Nat.succ_eq_add_one, hi']
        simp only [dif_neg hz] at hs
        simp only [Nat.cast_zero] at hinner
        rw [hupdate] at hinner
        have hinner' : (polyUnaryTM c C).tm.runFrom
            (polyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (polyCost q C i) =
            polyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (polyCost q C (i - 1) + 2) + q + 2 =
              polyCost q C i := by
            calc
              _ = polyCost q C (i - 1 + 1) := rfl
              _ = polyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show polyCost q C i + 2 = 1 + polyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (polyUnaryTM c C).tm.runFrom (polyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            polyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using poly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (polyUnaryTM c C).tm.step
          (polyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          polyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((polyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [polyUnaryTM, Cfg.workTapeSymbols, polyCfg, Function.update_self,
          polyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [polyCfg, sub_eq_add_neg] using polyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, poly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (polyCost q C i + 2) + q + 2 =
          (polyCost q C i + 2) + (r * (polyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma polyTape_write (q : ℕ) :
    Function.update (polyTape q) (q : ℤ) (some true) = polyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [polyTape]
  · rw [Function.update_of_ne hz]
    unfold polyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma polyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    polyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [polyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      polyCost q C (r + 1) = q * (polyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def polyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (PolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => polyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma poly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x) i =
      polyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, polyCopyCfg, polyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (polyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [polyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((polyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact polyTape_write i
    · funext k
      simp [polyUnaryTM, polyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma poly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (polyUnaryTM c C).tm.runFrom
      (polyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      polyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Cfg.workTapeSymbols, polyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (polyUnaryTM c C).tm.step
        (polyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        polyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Cfg.workTapeSymbols, polyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma poly_start (c C : ℕ) (x : List Bool) :
    (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      polyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (polyUnaryTM c C).tm.step
      (polyCopyCfg c C x x.length (le_refl _)) =
      polyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (polyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [polyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((polyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact polyTape_write x.length
    · funext k
      simp [polyUnaryTM, polyCopyCfg, polyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (polyUnaryTM c C).tm.runFrom ((polyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      polyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', poly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact poly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary polynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma poly_unary_computes (c C : ℕ) :
    (polyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := poly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (polyUnaryTM c C).tm.runFrom
      (polyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (polyCost (x.length + 1) C (c + 1)) =
      polyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [polyCost, hout] using hl
  have hbase : (polyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + polyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, poly_start, hloop]
    simp [MultiTapeTM.step, polyUnaryTM, polyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (polyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring

/-- **Polynomial bounds are time constructible**: for `C > 0`, the function
`n ↦ C·(n+1)^(c+1)` is `Complexity.TimeConstructible`. (A **new statement about
the Chapter-1 notion**, flagged for this phase's audit — see the deviations
list; the exponent `c + 1` keeps `T n ≥ n`, which degree `0` would violate.)
This is the plan's supporting obligation for the `TMSAT` reduction's unary
components.

**Proof sketch.** The bound `n ≤ n + 1 ≤ C·(n+1)^(c+1)` holds since `C ≥ 1`.
The machine: scan the input once, incrementing a little-endian binary counter
per cell to obtain `n` (the audited `Complexity.timeConstructible_id` fill is
the in-repo precedent; its private counter layer is a template, not a citable
API — phase-1 audit, finding 5); then compute `(n+1)^(c+1)` by `c + 1`
successive schoolbook binary multiplications and multiply by the constant `C`
(a fixed number of multiplications on operands of `O((c+1)·log(n+2) + log(C+1))`
bits, each polynomial in the bit length); emit the result as
`(T |x|).bits` (little-endian, the `Complexity.TimeConstructible` output
convention). Budget: the scan is `n` steps and the arithmetic polylogarithmic,
against the constant-slack budget `c'·(C·(n+1)^(c+1) + 1)` — ample.

**Implementation note (epoch 2).** The formal proof uses an exact unary
box-enumeration machine followed by the public linear-time binary length
counter, rather than formalizing schoolbook multiplication. Each of `c+1`
unary loop tapes has length `n+1`; each box point emits exactly `C` bits.
The generator costs at most `(C+5(c+1)+4)(n+1)^(c+1)`; timed composition with
`timeConstructible_id` preserves linear time in the polynomial's value.
This is a proof-route deviation only; the frozen statement is unchanged. -/
theorem timeConstructible_poly (C c : ℕ) (hC : 0 < C) :
    TimeConstructible fun n => C * (n + 1) ^ (c + 1) := by
  have hdom (n : ℕ) : (n + 1) ^ (c + 1) ≤ C * (n + 1) ^ (c + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((n + 1) ^ (c + 1)) hC
  refine ⟨fun n => ?_, ?_⟩
  · have hp : n + 1 ≤ (n + 1) ^ (c + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
        (show 1 ≤ c + 1 by omega)
    exact (Nat.le_succ n).trans (hp.trans (hdom n))
  · obtain ⟨_, a, ha, M, hM⟩ := timeConstructible_id
    have hcounter : M.ComputesFunInTime (fun x => x.length.bits) (fun n => a * (n + 1)) :=
      hM
    obtain ⟨N, b, hN⟩ := FinTM.computesFunInTime_comp (poly_unary_computes c C) hcounter
      (by intro m n h; exact Nat.mul_le_mul_left a (Nat.add_le_add_right h 1))
    let A := C + 5 * (c + 1) + 4
    refine ⟨(b + 1) * (a + 1) * (A + 1),
      Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _), N, ?_⟩
    intro x
    have hb := hN x
    simp only [Function.comp_apply, List.length_replicate] at hb
    apply hb.mono
    have hmajor : A * (x.length + 1) ^ (c + 1) + 1 ≤
        (A + 1) * (C * (x.length + 1) ^ (c + 1) + 1) := by
      have hm := Nat.mul_le_mul_left A (hdom x.length)
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    change b * (A * (x.length + 1) ^ (c + 1) +
        a * (A * (x.length + 1) ^ (c + 1) + 1) + 1) ≤ _
    calc
      _ = b * (a + 1) * (A * (x.length + 1) ^ (c + 1) + 1) := by ring
      _ ≤ (b + 1) * (a + 1) *
          ((A + 1) * (C * (x.length + 1) ^ (c + 1) + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right (a + 1) (Nat.le_succ b)) hmajor
      _ = _ := by ring

/-! ### Quantitative timed-universal bridge -/

/-- The canonizer's completed serialization cannot be longer than its run. -/
private lemma tmsat_serialization_length (c : EffectiveMachineCode) (α : List Bool) :
    (c.decode α).serialize.length ≤ c.canonizerTime α.length := by
  have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (c.canonizer_computes α)).2
  simpa only [hout] using c.canonizer.tm.output_length_le α (c.canonizerTime α.length)

/-- Flattening a nonempty word for each element cannot shorten a list. -/
private lemma tmsat_flatMap_length {A B : Type} (f : A → List B)
    (hf : ∀ a, 1 ≤ (f a).length) (l : List A) : l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := hf a
    omega

/-- Every transition record contains at least its two-bit input-head action. -/
private lemma tmsat_action_nonempty {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    1 ≤ (actionBits a).length := by
  have hs : 2 ≤ (signBits a.inputTape).length := by
    cases a.inputTape <;> exact Nat.le_refl 2
  change 1 ≤ (signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state).length
  simp only [List.length_append]
  omega

/-- The canonical serialization bounds the bit-header length, initial-state
index, and total number of states.

**Proof sketch.** The header contains the first two fields. Each state has a
nonempty transition record in the serialized table, so its number of records
also bounds the state count. This uses the public serialization definition. -/
private lemma tmsat_serialization_parameters (M : CodeTM) :
    (Nat.bits M.numStates).length ≤ M.serialize.length ∧
      M.tm.q₀.val ≤ M.serialize.length ∧ M.numStates + 1 ≤ M.serialize.length := by
  let f := fun q : Fin (M.numStates + 1) =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (M.tm.tr q inp fun _ => w)
  have hf (q : Fin (M.numStates + 1)) : 1 ≤ (f q).length := by
    dsimp only [f]
    simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_nil]
    have := tmsat_action_nonempty (M.tm.tr q none (fun _ => none))
    omega
  have htable : M.numStates + 1 ≤ ((List.finRange (M.numStates + 1)).flatMap f).length := by
    simpa only [List.length_finRange] using tmsat_flatMap_length f hf
      (List.finRange (M.numStates + 1))
  have hlen : M.serialize.length = 2 * (Nat.bits M.numStates).length + 2 +
      (M.tm.q₀.val + 1 + ((List.finRange (M.numStates + 1)).flatMap f).length) := by
    change (pairEncode (Nat.bits M.numStates)
      ((List.replicate M.tm.q₀.val true ++ [false]) ++
        (List.finRange (M.numStates + 1)).flatMap f)).length = _
    simp only [universal_pair_length, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
  rw [hlen]
  omega

/-- The concrete coefficient displayed in the private timed-simulator proof
is bounded by the mandated public bridge's closed coefficient.

**Proof sketch.** The serialization, header length, initial index, and state
count are each bounded by the canonizer time. Expanding the concrete startup
and block coefficients gives one canonizer term plus thirteen such bounded
terms and constant fifty. This is solely an arithmetic bound on the displayed
expression, not a bound on `timed_universal`'s arbitrary existential witness. -/
private lemma tmsat_concrete_coefficient (c : EffectiveMachineCode) (α : List Bool) :
    3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
      2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16 +
      universalBlockBound c α + 14 ≤ 3 * α.length + 14 * c.canonizerTime α.length + 50 := by
  have hlen := tmsat_serialization_length c α
  obtain ⟨hbits, hstart, hstates⟩ := tmsat_serialization_parameters (c.decode α)
  unfold universalBlockBound
  omega

/-- A single timed simulator, selected before the code and input, preserves
both successful completion and timeout with the explicit budget
`(3|α| + 14*canonizerTime(|α|) + 50)*(t+1)^2`.
[AB09, §1.4.1, time-bounded universal simulation], with explicit constants.

**The phase-3-mandated bridge statement: new public surface for the epoch-2
audit.** Its coefficient is the displayed function of the code length; no
bound on an arbitrary existential witness of `Turing.timed_universal` is asserted.

**Proof sketch and escalation (bridge protocol, step 3).** Reuse the concrete
timed simulator's construction, bound the decoded serialization length by the
canonizer's output-time bound, and bound the state/header sizes by that
serialization. The existing proof's coefficient is then at most the displayed
coefficient. At this pin, the concrete simulator `timedUniversalTM`, its
`timedStartupBound`, and its exact bounded-answer lemma `timed_computes` in
`Universal.lean` are private. The public API exposes only the existential
coefficient, so the construction cannot be reused through that API. This single
bridge declaration is intentionally admitted under the brief's escalation
protocol: the maintainer must export a quantitative concrete bounded-answer
lemma from Chapter 1 (including its timeout branch) and discharge this proof.
Chapter-1 sources are unchanged.

**Discharged (2026-10-03, maintainer serial merge).** Chapter 1 now exports
`Turing.timed_universal_concrete`: the concrete simulator's bounded-answer
theorem with the private startup expression expanded into public vocabulary
and both clauses preserved. This proof is that export, the arithmetic bound
`tmsat_concrete_coefficient` on its displayed coefficient, and
`Turing.FinTM.ComputesInTime.mono`. The escalation paragraph above is
retained as audit history; its final sentence described the pre-export
state, and the export is flagged for the shared infrastructure audit
round. -/
theorem timed_universal_quantitative (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output)
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false]
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) := by
  obtain ⟨U, hU⟩ := timed_universal_concrete c
  refine ⟨U, fun α x t => ?_⟩
  obtain ⟨hsucc, htimeout⟩ := hU α x t
  have hle : (3 * α.length + c.canonizerTime α.length +
      (c.decode α).serialize.length +
      2 * (Nat.bits (c.decode α).numStates).length +
      2 * (c.decode α).tm.q₀.val + 16 +
      universalBlockBound c α + 14) * (t + 1) ^ 2 ≤
      (3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2 :=
    Nat.mul_le_mul_right _ (tmsat_concrete_coefficient c α)
  exact ⟨fun output hout => (hsucc output hout).mono hle,
    fun hnone => (htimeout hnone).mono hle⟩

/-- The exact success-tagged output or timeout answer of a bounded source run. -/
private def tmsatAnswer (c : MachineCode) (α x : List Bool) (t : ℕ) : List Bool :=
  let cfg := (c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t
  if cfg.state = none then true :: cfg.output else [false]

/-- Both clauses of the quantitative bridge yield a completed answer for every
well-formed timed request, including divergent source computations.

**Proof sketch.** Inspect the source configuration at the deadline. A halted
configuration witnesses completed computation with its full output. A live
configuration rules out every completed output, activating the timeout clause. -/
private lemma tmsat_simulator_total (c : EffectiveMachineCode) (U : FinTM Bool)
    (hU : ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool, (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) (true :: output)
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2)))
    (α x : List Bool) (t : ℕ) :
    U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
      (tmsatAnswer c.toMachineCode α x t)
      ((3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1) ^ 2) := by
  by_cases hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none
  · have hs := (FinTM.computesInTime_iff (c.decode α).toFinTM x
      (((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output) t).mpr ⟨hh, rfl⟩
    simpa only [tmsatAnswer, if_pos hh] using (hU α x t).1 _ hs
  · have hs : ∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t := by
      intro output ho
      exact hh ((FinTM.computesInTime_iff _ _ _ _).mp ho).1
    simpa only [tmsatAnswer, if_neg hh] using (hU α x t).2 hs

/-- Acceptance compares the entire captured answer with `[true,true]`;
timeouts and successful runs with any other completed output are rejected. -/
private lemma tmsatAnswer_accept (c : MachineCode) (α x : List Bool) (t : ℕ) :
    tmsatAnswer c α x t = [true, true] ↔
      (c.decode α).toFinTM.ComputesInTime x [true] t := by
  rw [FinTM.computesInTime_iff]
  dsimp only [tmsatAnswer]
  split <;> simp_all [CodeTM.toFinTM]

/-- The polynomial canonizer hypothesis gives one polynomial budget, uniform
over every code length and unary deadline bounded by the instance length.

**Proof sketch.** Bound both the linear code-length term and the canonizer
majorant by a power of degree `max 1 e`. Absorb the constant term into the
same positive power and multiply by the deadline's quadratic bound. No
monotonicity of the canonizer time itself is assumed. -/
private lemma tmsat_simulation_budget (c : EffectiveMachineCode)
    (hc : PolyBound c.canonizerTime) :
    ∃ A d : ℕ, ∀ m r t : ℕ, r ≤ m → t ≤ m →
      (3 * r + 14 * c.canonizerTime r + 50) * (t + 1) ^ 2 ≤ A * (m + 1) ^ d := by
  obtain ⟨C, e, he⟩ := hc
  refine ⟨3 + 14 * C + 50, max 1 e + 2, ?_⟩
  intro m r t hr ht
  have hp : 1 ≤ (m + 1) ^ max 1 e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hrp : r ≤ (m + 1) ^ max 1 e := by
    calc r ≤ m + 1 := by omega
      _ = (m + 1) ^ 1 := by simp
      _ ≤ (m + 1) ^ max 1 e := Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_left _ _)
  have hH : c.canonizerTime r ≤ C * (m + 1) ^ max 1 e := by
    calc c.canonizerTime r ≤ C * (r + 1) ^ e := he r
      _ ≤ C * (m + 1) ^ e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) e)
      _ ≤ C * (m + 1) ^ max 1 e :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_max_right _ _))
  have hcoef : 3 * r + 14 * c.canonizerTime r + 50 ≤
      (3 + 14 * C + 50) * (m + 1) ^ max 1 e := by
    simp only [Nat.add_mul, Nat.mul_assoc]
    omega
  calc
    _ ≤ ((3 + 14 * C + 50) * (m + 1) ^ max 1 e) * (m + 1) ^ 2 :=
      Nat.mul_le_mul hcoef (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by rw [Nat.mul_assoc, ← Nat.pow_add]

/-- The right-nested quadruple used by `TMSAT`, with exact unary fields. -/
private def tmsatQuad (α x : List Bool) (n t : ℕ) : List Bool :=
  pairEncode α (pairEncode x (pairEncode (List.replicate n true) (List.replicate t true)))

/-- All four tuple components fit inside the full encoded instance. -/
private lemma tmsat_quad_bounds (α x : List Bool) (n t : ℕ) :
    α.length ≤ (tmsatQuad α x n t).length ∧ x.length ≤ (tmsatQuad α x n t).length ∧
      n ≤ (tmsatQuad α x n t).length ∧ t ≤ (tmsatQuad α x n t).length := by
  simp only [tmsatQuad, universal_pair_length, List.length_replicate]
  omega

/-- The verifier specification uses an exact odd-length split, parses the
quadruple, and tests only the requested prefix of the padded certificate. -/
private def tmsatVerifier (c : MachineCode) : Language Bool :=
  {z | ∃ (y w α x : List Bool) (n t : ℕ),
    z = y ++ w ∧ w.length = y.length + 1 ∧ y = tmsatQuad α x n t ∧
      (c.decode α).toFinTM.ComputesInTime (pairEncode x (w.take n)) [true] t}

/-- Exact certificates force odd total length and recover the split position uniquely. -/
private lemma tmsat_split_length (y w : List Bool) (hw : w.length = y.length + 1) :
    (y ++ w).length % 2 = 1 ∧ ((y ++ w).length - 1) / 2 = y.length := by
  simp only [List.length_append, hw]
  omega

/-- The exact `m+1`-bit certificate convention is equivalent to the language's
original `n`-bit witness. No certificate-length majorization changes the source run.

**Proof sketch.** Pad the original witness with false bits and recover it by
taking its first `n` bits. Conversely, equality of the two concatenations and
their exact certificate lengths forces equal split positions, so the accepted
prefix has length exactly `n`. The tuple's unary field bounds `n` by `m`. -/
private lemma tmsat_certificate_equiv (c : MachineCode) (y : List Bool) :
    y ∈ TMSAT c ↔ ∃ w : List Bool, w.length = y.length + 1 ∧ y ++ w ∈ tmsatVerifier c := by
  constructor
  · rintro ⟨α, x, u, n, t, hy, hu, hs⟩
    have hn : n ≤ y.length := by
      rw [hy]
      exact (tmsat_quad_bounds α x n t).2.2.1
    let w := u ++ List.replicate (y.length + 1 - n) false
    have hw : w.length = y.length + 1 := by
      simp only [w, List.length_append, List.length_replicate, hu]
      omega
    refine ⟨w, hw, y, w, α, x, n, t, rfl, hw, hy, ?_⟩
    have htake : w.take n = u := List.take_left' hu
    rw [htake]
    exact hs
  · rintro ⟨w, hw, y', w', α, x, n, t, he, hw', hy, hs⟩
    have hlen := congrArg List.length he
    simp only [List.length_append, hw, hw'] at hlen
    obtain ⟨rfl, rfl⟩ := List.append_inj he (by omega)
    refine ⟨α, x, w.take n, n, t, hy, ?_, hs⟩
    have hn : n ≤ y.length := by
      rw [hy]
      exact (tmsat_quad_bounds α x n t).2.2.1
    rw [List.length_take, Nat.min_eq_left (by omega : n ≤ w.length)]

/-- The library's pair-to-concatenation function, including malformed inputs. -/
private def tmsatConcat (z : List Bool) : List Bool :=
  match pairDecode z with | some (a,b) => a ++ b | none => []

/-- Equality with an entire fixed answer is a polynomial-time bit test. -/
private lemma tmsat_pt_eq (w : List Bool) :
    PolyTimeComputable (fun x => [decide (x = w)]) := by
  have h := polyTimeComputable_of_linear (FinTM.computesFunInTime_ifEq w [true] [false])
  convert h using 1
  funext x
  by_cases hx : x = w <;> simp [hx]

/-- A fixed-width increment never successfully returns the empty word. -/
private lemma tmsat_inc_nonempty (w : List Bool) : incFixed w ≠ some [] := by
  cases w with
  | nil => simp [incFixed]
  | cons b w => cases b <;> cases h : incFixed w <;> simp [incFixed, h]

/-- Overflow is exactly the all-true unary shape, including length zero. -/
private lemma tmsat_inc_none (w : List Bool) :
    incFixed w = none ↔ w = List.replicate w.length true := by
  induction w with
  | nil => simp [incFixed]
  | cons b w ih => cases b <;> simp [incFixed, List.replicate_succ, ih]

/-- The exact all-true shape is decided by P11 overflow and whole-word equality. -/
private lemma tmsat_pt_unary :
    PolyTimeComputable (fun x => [decide (x = List.replicate x.length true)]) := by
  have h := (tmsat_pt_eq []).comp (polyTimeComputable_of_linear FinTM.computesFunInTime_incFixed)
  convert h using 1
  funext x
  have he : (incFixed x).getD [] = [] ↔ x = List.replicate x.length true := by
    rw [← tmsat_inc_none]
    cases hi : incFixed x with
    | none => simp
    | some w =>
      have hw : w ≠ [] := by intro hw; subst w; exact tmsat_inc_nonempty x hi
      simp [hw]
  simp only [Function.comp_apply, he]

/-- Count doubled prefix cells on a unary work tape, then emit at most that
many native payload bits while moving the work head left. The output stays
silent until the separator; the public use supplies only constructed pairs. -/
private def tmsatTakeTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm := { q₀ := 0, tr := fun q inp w =>
    if q = 0 then
      match inp with
      | some b => ⟨1, fun _ => (none, 0), none, some (if b then 2 else 1)⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩
    else if q = 1 then
      match inp with
      | some false => ⟨1, fun _ => (some (some true), 1), none, some 0⟩
      | some true => ⟨1, fun _ => (none, -1), none, some 3⟩
      | none => ⟨0, fun _ => (none, 0), none, none⟩
    else if q = 2 then
      match inp with
      | some true => ⟨1, fun _ => (some (some true), 1), none, some 0⟩
      | _ => ⟨0, fun _ => (none, 0), none, none⟩
    else
      match w 0, inp with
      | some _, some b => ⟨1, fun _ => (none, -1), some b, some 3⟩
      | _, _ => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Prefix-extractor configurations record both the allocated unary interval
and its current head; the native input index is the number of consumed bits. -/
private def tmsatTakeCfg (x : List Bool) (q : Option (Fin 4))
    (i : ℕ) (hi : i ≤ x.length) (m : ℕ) (h : ℤ) (out : List Bool) :
    Cfg 1 Bool (Fin 4) x :=
  ⟨q, ⟨i+1, by omega⟩, fun _ => polyTape m, fun _ => h, out⟩

/-- Exact one-step input lookup for the indexed extractor configuration. -/
private lemma tmsat_take_read (x : List Bool) (q : Option (Fin 4))
    (i : ℕ) (hi : i ≤ x.length) (m : ℕ) (h : ℤ) (out : List Bool) :
    (tmsatTakeCfg x q i hi m h out).inputSymbol = x[i]? := by
  exact FinTM.inputSymbol_at _ i hi rfl

/-- Two equal prefix bits append precisely one unary counter cell. -/
private lemma tmsat_take_double (x : List Bool) (i m : ℕ) (b : Bool)
    (hi : i + 2 ≤ x.length) (h₀ : x[i]? = some b) (h₁ : x[i+1]? = some b) :
    tmsatTakeTM.tm.runFrom (tmsatTakeCfg x (some 0) i (by omega) m m []) 2 =
      tmsatTakeCfg x (some 0) (i+2) hi (m+1) (m+1) [] := by
  have hs : tmsatTakeTM.tm.step (tmsatTakeCfg x (some 0) i (by omega) m m []) =
      tmsatTakeCfg x (some (if b then 2 else 1)) (i+1) (by omega) m m [] := by
    change (tmsatTakeTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [tmsat_take_read, h₀]
    change (⟨1, fun _ => (none, 0), none, some (if b then 2 else 1)⟩ :
      Action 1 Bool (Fin 4)).apply _ = _
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; omega)
    · rfl
    · funext j; simp [Action.apply, tmsatTakeCfg]
    · rfl
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (tmsatTakeTM.tm.tr (if b then (2 : Fin 4) else (1 : Fin 4)) _ _).apply _ = _
  rw [tmsat_take_read, h₁]
  cases b <;>
    change (⟨1, fun _ => (some (some true), 1), none, some 0⟩ :
      Action 1 Bool (Fin 4)).apply _ = _
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; omega)
    · funext j; exact polyTape_write m
    · funext j; simp [Action.apply, tmsatTakeCfg]
    · rfl

/-- The separator consumes two native bits and places the counter at its last cell. -/
private lemma tmsat_take_separator (x : List Bool) (i m : ℕ)
    (hi : i + 2 ≤ x.length) (h₀ : x[i]? = some false) (h₁ : x[i+1]? = some true) :
    tmsatTakeTM.tm.runFrom (tmsatTakeCfg x (some 0) i (by omega) m m []) 2 =
      tmsatTakeCfg x (some 3) (i+2) hi m ((m : ℤ)-1) [] := by
  have hs : tmsatTakeTM.tm.step (tmsatTakeCfg x (some 0) i (by omega) m m []) =
      tmsatTakeCfg x (some 1) (i+1) (by omega) m m [] := by
    change (tmsatTakeTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [tmsat_take_read, h₀]
    change (⟨1, fun _ => (none, 0), none, some 1⟩ : Action 1 Bool (Fin 4)).apply _ = _
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; omega)
    · rfl
    · funext j; simp [Action.apply, tmsatTakeCfg]
    · rfl
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  change (tmsatTakeTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  rw [tmsat_take_read, h₁]
  change (⟨1, fun _ => (none, -1), none, some 3⟩ : Action 1 Bool (Fin 4)).apply _ = _
  apply Cfg.ext
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; omega)
  · rfl
  · funext j; simp [Action.apply, tmsatTakeCfg, sub_eq_add_neg]
  · rfl

/-- The aligned parser installs exactly the first component's length.

**Proof sketch.** Induct on the remaining doubled prefix, preserving an
arbitrary already-counted prefix. Each pair costs two steps; the separator
costs two more. No native payload bit has yet been emitted. -/
private lemma tmsat_take_parse (a b : List Bool) :
    ∀ (x pre : List Bool) (m : ℕ) (hx : x = pre ++ pairEncode a b),
    tmsatTakeTM.tm.runFrom
      (tmsatTakeCfg x (some 0) pre.length (by simp [hx, pairEncode]) m m [])
      (2*a.length+2) =
    tmsatTakeCfg x (some 3) (pre.length+2*a.length+2)
      (by simp [hx, universal_pair_length]; omega)
      (m+a.length) ((m+a.length : ℕ)-1 : ℤ) [] := by
  induction a with
  | nil =>
    intro x pre m hx
    have h₀ : x[pre.length]? = some false := by simp [hx, pairEncode]
    have h₁ : x[pre.length+1]? = some true := by simp [hx, pairEncode]
    simpa using tmsat_take_separator x pre.length m (by simp [hx, pairEncode]) h₀ h₁
  | cons v a ih =>
    intro x pre m hx
    have hx' : x = (pre ++ [v,v]) ++ pairEncode a b := by
      simpa [pairEncode, List.append_assoc] using hx
    have hs := tmsat_take_double x pre.length m v
      (by simp [hx', List.length_append])
      (by simp [hx', List.append_assoc]) (by simp [hx', List.append_assoc])
    conv_lhs => arg 2; rw [show 2*(v::a).length+2 = 2+(2*a.length+2) by simp; omega]
    rw [MultiTapeTM.runFrom_add, hs]
    have h := ih x (pre ++ [v,v]) (m+1) hx'
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add,
      Nat.mul_one, Nat.cast_add, Nat.cast_one, Nat.reduceAdd] using h

/-- The payload phase emits the exact requested prefix, even if the request
exceeds the payload length; it stops at either boundary.

**Proof sketch.** Induct on the number of emitted bits up to the minimum of
the counter and payload lengths. Every step preserves the unary tape and
moves its head left. The next step sees either the left blank or the native
right boundary and halts without an additional bit. -/
private lemma tmsat_take_payload (x pre b : List Bool) (hx : x = pre ++ b) (m : ℕ) :
    ∀ j (hj : j ≤ min m b.length),
      tmsatTakeTM.tm.runFrom
        (tmsatTakeCfg x (some 3) pre.length (by simp [hx]) m ((m:ℤ)-1) []) j =
      tmsatTakeCfg x (some 3) (pre.length+j) (by simp [hx] ; omega)
        m ((m:ℤ)-j-1) (b.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [tmsatTakeCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    change (tmsatTakeTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [tmsat_take_read]
    have hr : x[pre.length+j]? = some b[j] := by
      simp only [hx, List.getElem?_append_right (by omega : pre.length ≤ pre.length+j),
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem (show j < b.length by omega)]
    rw [hr]
    have hw : (tmsatTakeCfg x (some 3) (pre.length+j) (by simp [hx] ; omega)
        m ((m:ℤ)-j-1) (b.take j)).workTapeSymbols 0 = some true := by
      simp [tmsatTakeCfg, Cfg.workTapeSymbols, polyTape,
        show 0 ≤ (m:ℤ)-j-1 ∧ (m:ℤ)-j-1 < m by omega] ; omega
    simp only [tmsatTakeTM, show (3:Fin 4) ≠ 0 by decide, if_false,
      show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by dsimp [tmsatTakeCfg]; simp only [hx, List.length_append]; omega)
    · rfl
    · funext i; simp [Action.apply, tmsatTakeCfg]; omega
    · simp only [Action.apply, tmsatTakeCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- On every constructed pair, prefix extraction takes at most input length
plus one steps. Malformed-input behavior is never invoked by the assembly. -/
private lemma tmsat_take_computes (a b : List Bool) :
    tmsatTakeTM.ComputesInTime (pairEncode a b) (b.take a.length)
      ((pairEncode a b).length+1) := by
  let x := pairEncode a b
  let pre := (a.flatMap fun v => [v,v]) ++ [false,true]
  have hx : x = pre ++ b := rfl
  have hp : pre.length = 2*a.length+2 := by
    have h := universal_pair_length a ([] : List Bool)
    simpa [pre, pairEncode] using h
  have hs := tmsat_take_parse a b x [] 0 rfl
  simp only [List.length_nil, Nat.zero_add, Nat.cast_zero] at hs
  have hi : tmsatTakeTM.tm.initCfg x = tmsatTakeCfg x (some 0) 0 (by omega) 0 0 [] := by
    apply Cfg.ext <;> simp [tmsatTakeCfg, tmsatTakeTM]
    funext i z
    simp [polyTape]
  have hrun : tmsatTakeTM.tm.runFrom (tmsatTakeTM.tm.initCfg x)
      (2*a.length+2+min a.length b.length) =
      tmsatTakeCfg x (some 3) (pre.length+min a.length b.length)
        (by simp [hx] ) a.length
        ((a.length:ℤ)-min a.length b.length-1) (b.take (min a.length b.length)) := by
    rw [MultiTapeTM.runFrom_add, hi, hs]
    simpa only [List.length_nil, Nat.zero_add, hp] using
      tmsat_take_payload x pre b hx a.length (min a.length b.length) (by omega)
  have ht : tmsatTakeTM.ComputesInTime x (b.take a.length)
      (2*a.length+2+min a.length b.length+1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', hrun]
    change ((tmsatTakeTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧
      ((tmsatTakeTM.tm.tr (3 : Fin 4) _ _).apply _).output = b.take a.length
    rw [tmsat_take_read]
    have hend :
      polyTape a.length ((a.length:ℤ)-min a.length b.length-1) = none ∨
        x[pre.length+min a.length b.length]? = none := by
      by_cases h : a.length ≤ b.length
      · left; simp [Nat.min_eq_left h, polyTape]
      · right; simp [Nat.min_eq_right (by omega : b.length ≤ a.length), hx]
    rcases hend with hw | hr
    · simp [tmsatTakeTM, tmsatTakeCfg, Cfg.workTapeSymbols, hw, Action.apply,
        List.take_eq_take_min]
    · simp [tmsatTakeTM, tmsatTakeCfg, Cfg.workTapeSymbols, hr, Action.apply,
        List.take_eq_take_min]
  apply ht.mono
  dsimp [x]
  rw [universal_pair_length]
  omega

/-- The prefix extractor is used only on pairs made by the §9c assembly.
Its time is bounded by that preprocessor's actual output-length guarantee. -/
private lemma tmsat_pt_take {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => (g x).take (f x).length) := by
  obtain ⟨M, C, e, hM⟩ := hf.pairEncode hg
  have hT (x : List Bool) : tmsatTakeTM.ComputesInTime (pairEncode (f x) (g x))
      ((g x).take (f x).length) (C * (x.length+1)^e+1) := by
    apply (tmsat_take_computes (f x) (g x)).mono
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
    have hl := M.tm.output_length_le x (C * (x.length+1)^e)
    rw [ho] at hl
    dsimp only at hl
    omega
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M tmsatTakeTM _ (fun x => (g x).take (f x).length)
    (fun n => C*(n+1)^e) (fun n => C*(n+1)^e+1) hM hT
  refine ⟨N, 3*(C+1), e, fun x => (hN x).mono ?_⟩
  have hp : 1 ≤ (x.length+1)^e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  dsimp only
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
  omega

/-- On valid inputs the projections reconstruct the pair. -/
private lemma tmsat_pair_valid (z : List Bool) (h : (pairDecode z).isSome = true) :
    z = pairEncode (pairFstD z) (pairSndD z) := by
  cases hd : pairDecode z with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨a,b⟩
    simpa only [pairFstD, pairSndD, hd, Option.map_some, Option.getD_some] using
      eq_pairEncode_of_pairDecode z a b hd

/-- The exact odd split is the P10 search at coefficient and degree one. -/
private def tmsatSplit (z : List Bool) : List Bool :=
  match solveSplit 1 1 z.length with
  | some i => pairEncode (z.take i) (z.drop i)
  | none => []

/-- A successful split has precisely the required length equation. -/
private lemma tmsat_split_some (N i : ℕ) (h : solveSplit 1 1 N = some i) :
    i + (i+1) = N := by
  have he := List.find?_some h
  simpa [Nat.pow_one] using he

/-- If the exact length equation has a solution, P10 returns that solution.
Any returned index satisfies the same strictly increasing linear equation. -/
private lemma tmsat_split_exists (N i : ℕ) (h : i+(i+1)=N) :
    solveSplit 1 1 N = some i := by
  cases hs : solveSplit 1 1 N with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp; omega)
    simp [h] at hn
  | some j =>
    have hj := tmsat_split_some N j hs
    congr 1
    omega

/-- The exact split gives back the original instance and padded certificate. -/
private lemma tmsat_split_append (y w : List Bool) (hw : w.length=y.length+1) :
    tmsatSplit (y++w) = pairEncode y w := by
  unfold tmsatSplit
  rw [tmsat_split_exists (y++w).length y.length (by simp [hw])]
  simp

/-- Both halves of a successful odd split retain their original native lengths. -/
private lemma tmsat_split_components (z : List Bool)
    (h : (pairDecode (tmsatSplit z)).isSome = true) :
    z = pairFstD (tmsatSplit z) ++ pairSndD (tmsatSplit z) ∧
    (pairSndD (tmsatSplit z)).length = (pairFstD (tmsatSplit z)).length+1 := by
  cases hs : solveSplit 1 1 z.length with
  | none => simp [tmsatSplit, hs, pairDecode] at h
  | some i =>
    have hi := tmsat_split_some z.length i hs
    simp only [tmsatSplit, hs, pairFstD, pairSndD, pairDecode_pairEncode,
      Option.map_some, Option.getD_some]
    refine ⟨(List.take_append_drop i z).symm, ?_⟩
    simp only [List.length_take, List.length_drop]
    omega

/-- The parsed instance is the first exact-split component. -/
private def tmsatY (z : List Bool) : List Bool := pairFstD (tmsatSplit z)

/-- The padded certificate is the second exact-split component. -/
private def tmsatW (z : List Bool) : List Bool := pairSndD (tmsatSplit z)

/-- The retained code field. -/
private def tmsatCode (z : List Bool) : List Bool := pairFstD (tmsatY z)

/-- The retained source input field. -/
private def tmsatInput (z : List Bool) : List Bool := pairFstD (pairSndD (tmsatY z))

/-- The unary certificate-length field, before shape validation. -/
private def tmsatWidth (z : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (tmsatY z)))

/-- The unary deadline field, before shape validation. -/
private def tmsatClock (z : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (tmsatY z)))

/-- Grammar guards precede projections at all three quadruple spine levels;
then both unary fields are checked in full, including the empty word. -/
private def tmsatGood (z : List Bool) : Bool :=
  (pairDecode (tmsatSplit z)).isSome &&
  ((pairDecode (tmsatY z)).isSome &&
  ((pairDecode (pairSndD (tmsatY z))).isSome &&
  ((pairDecode (pairSndD (pairSndD (tmsatY z)))).isSome &&
  (decide (tmsatWidth z = List.replicate (tmsatWidth z).length true) &&
   decide (tmsatClock z = List.replicate (tmsatClock z).length true)))))

/-- Successful guards reconstruct the exact quadruple and split equation. -/
private lemma tmsat_good_spec (z : List Bool) (h : tmsatGood z = true) :
    z = tmsatY z ++ tmsatW z ∧ (tmsatW z).length = (tmsatY z).length+1 ∧
    tmsatY z = tmsatQuad (tmsatCode z) (tmsatInput z)
      (tmsatWidth z).length (tmsatClock z).length := by
  simp only [tmsatGood, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, hy, hx, hn, hwidth, hclock⟩ := h
  obtain ⟨hz, hw⟩ := tmsat_split_components z hs
  refine ⟨hz, hw, ?_⟩
  have h₀ := tmsat_pair_valid (tmsatY z) hy
  have h₁ := tmsat_pair_valid (pairSndD (tmsatY z)) hx
  have h₂ := tmsat_pair_valid (pairSndD (pairSndD (tmsatY z))) hn
  change tmsatY z = pairEncode (tmsatCode z)
    (pairEncode (tmsatInput z) (pairEncode (List.replicate _ true) (List.replicate _ true)))
  rw [← hwidth, ← hclock]
  exact h₀.trans (congrArg (pairEncode (tmsatCode z))
    (h₁.trans (congrArg (pairEncode (tmsatInput z)) h₂)))

/-- Every well-formed quadruple with its padded witness passes every guard,
and all fields are recovered literally. -/
private lemma tmsat_good_quad (α x w : List Bool) (n t : ℕ)
    (hw : w.length = (tmsatQuad α x n t).length+1) :
    let z := tmsatQuad α x n t ++ w
    tmsatGood z = true ∧ tmsatCode z = α ∧ tmsatInput z = x ∧
      (tmsatWidth z).length = n ∧ (tmsatClock z).length = t ∧ tmsatW z = w := by
  dsimp only
  simp only [tmsatGood, tmsatCode, tmsatInput, tmsatWidth, tmsatClock, tmsatW, tmsatY]
  simp only [tmsat_split_append _ _ hw]
  simp [tmsatQuad, pairFstD, pairSndD, pairDecode_pairEncode]

/-- Computed fields and ordered validation use P10, P6, P11, and W3.
Each projection consumes the preceding computed word; validity is still
checked separately before its result can enter an accepted request. -/
private lemma tmsat_fields_poly :
    PolyTimeComputable tmsatCode ∧ PolyTimeComputable tmsatInput ∧
    PolyTimeComputable tmsatWidth ∧ PolyTimeComputable tmsatClock ∧
    PolyTimeComputable tmsatW ∧ PolyTimeComputable (fun z => [tmsatGood z]) := by
  obtain ⟨S, A, hS⟩ := FinTM.computesFunInTime_splitSolve 1 1
  have hsplit : PolyTimeComputable tmsatSplit := ⟨S,A,3,hS⟩
  have hf : PolyTimeComputable pairFstD := polyTimeComputable_pairFstD
  have hs : PolyTimeComputable pairSndD := polyTimeComputable_pairSndD
  have hv := polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid
  have hy : PolyTimeComputable tmsatY := hf.comp hsplit
  have h₁ := hs.comp hy
  have h₂ := hs.comp h₁
  have hn : PolyTimeComputable tmsatWidth := hf.comp h₂
  have ht : PolyTimeComputable tmsatClock := hs.comp h₂
  refine ⟨hf.comp hy, hf.comp h₁, hn, ht, hs.comp hsplit, ?_⟩
  exact polyTimeComputable_and (hv.comp hsplit) (polyTimeComputable_and (hv.comp hy)
    (polyTimeComputable_and (hv.comp h₁) (polyTimeComputable_and (hv.comp h₂)
      (polyTimeComputable_and (tmsat_pt_unary.comp hn) (tmsat_pt_unary.comp ht)))))

/-- Invalid requests are replaced by a well-formed zero-deadline request,
so the simulator is used only on its proved totality domain. -/
private def tmsatRequest (z : List Bool) : List Bool :=
  if tmsatGood z then
    pairEncode (pairEncode (Nat.bits (tmsatClock z).length) (tmsatCode z))
      (pairEncode (tmsatInput z) ((tmsatW z).take (tmsatWidth z).length))
  else pairEncode (pairEncode [] []) []

/-- The exact completed answer associated with preprocessing. -/
private def tmsatResult (c : MachineCode) (z : List Bool) : List Bool :=
  if tmsatGood z then
    tmsatAnswer c (tmsatCode z)
      (pairEncode (tmsatInput z) ((tmsatW z).take (tmsatWidth z).length))
      (tmsatClock z).length
  else tmsatAnswer c [] [] 0

/-- Construct the guarded timed request by the canonical §9c pairing recipe.

**Proof sketch.** Retain the whole request as the head of a pair while C1
runs the binary length counter on the unary clock payload. Pair the extracted
binary clock with the recovered code, and the recovered source input with
the exact prefix extractor's output. W3 chooses that request only after all
guards succeed, otherwise emitting the fixed zero-deadline request. -/
private lemma tmsat_request_poly : PolyTimeComputable tmsatRequest := by
  obtain ⟨ha,hx,hn,ht,hw,hgood⟩ := tmsat_fields_poly
  have hb := polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits
  have hs := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  have hclock : PolyTimeComputable (fun z => Nat.bits (tmsatClock z).length) := by
    have h := hs.comp (hb.pairMapSnd.comp (polyTimeComputable_id.pairEncode ht))
    convert h using 1
    funext z
    simp [Function.comp_apply, pairMapSnd, pairDecode_pairEncode]
  exact polyTimeComputable_ite hgood
    ((hclock.pairEncode ha).pairEncode (hx.pairEncode (tmsat_pt_take hn hw)))
    (polyTimeComputable_const (pairEncode (pairEncode [] []) []))

/-- Valid code lengths and unary deadlines are bounded by the original
verifier input length, so the simulator consumes the proved uniform budget. -/
private lemma tmsat_good_bounds (z : List Bool) (h : tmsatGood z = true) :
    (tmsatCode z).length ≤ z.length ∧ (tmsatClock z).length ≤ z.length := by
  obtain ⟨hz, hw, hy⟩ := tmsat_good_spec z h
  have hb := tmsat_quad_bounds (tmsatCode z) (tmsatInput z)
    (tmsatWidth z).length (tmsatClock z).length
  rw [← hy] at hb
  have hlen := congrArg List.length hz
  simp only [List.length_append] at hlen
  omega

/-- The guarded simulator's whole-answer test is exactly the existential
verifier specification, including rejection of every invalid request.

**Proof sketch.** Successful guards reconstruct the original split and
quadruple, and `tmsatAnswer_accept` identifies the source acceptance event.
Conversely every witness of the specification passes all guards and is
recovered literally. A failed guard uses deadline zero, where the source
machine cannot have halted. -/
private lemma tmsat_result_accept (c : MachineCode) (z : List Bool) :
    tmsatResult c z = [true,true] ↔ z ∈ tmsatVerifier c := by
  constructor
  · intro h
    by_cases hg : tmsatGood z = true
    · obtain ⟨hz, hw, hy⟩ := tmsat_good_spec z hg
      simp only [tmsatResult, hg, ↓reduceIte, tmsatAnswer_accept] at h
      exact ⟨tmsatY z, tmsatW z, tmsatCode z, tmsatInput z,
        (tmsatWidth z).length, (tmsatClock z).length, hz, hw, hy, h⟩
    · have hzero : ¬(c.decode []).toFinTM.ComputesInTime [] [true] 0 :=
        FinTM.not_computesInTime_zero _ _ _
      simp only [tmsatResult, if_neg hg, tmsatAnswer_accept] at h
      exact (hzero h).elim
  · rintro ⟨y,w,α,x,n,t,hz,hw,hy,hs⟩
    subst y
    subst z
    obtain ⟨hg,ha,hx,hn,ht,hw'⟩ := tmsat_good_quad α x w n t hw
    simp only [tmsatResult, hg, ↓reduceIte, ha, hx, hn, ht, hw', tmsatAnswer_accept]
    exact hs

/-- **`TMSAT ∈ NP` for polynomially canonizable schemes** [AB09, Theorem 2.9,
membership]: the certificate is `u` itself, and verification is timed
universal simulation. The hypothesis `Complexity.PolyBound c.canonizerTime`
is **load-bearing and cannot be dropped** (round-1 audit, finding 1,
Argument A): `Turing.EffectiveMachineCode` constrains the canonizer's
*computability*, not its cost, and there is a lawful effective scheme — the
base scheme behind a one-bit tag, with the tagged branch decoding `[1] ++ z`
to a one-step machine that outputs the bit `A z` of a decidable language
`A ∉ EXP` — whose `TMSAT` decides `A` on the trivial instances
`⟨[1] ++ z, [], 1^0, 1^1⟩`; membership in `NP ⊆ EXP` would contradict
`A ∉ EXP`. The polynomial canonizer bound is what restores a uniform
simulation budget.

**Proof sketch.** Certificate parameters `(1, 1)`: length exactly `m + 1` on
inputs of length `m` (the declared `n` satisfies `n ≤ m`, since `1^n` sits
inside `y`; the certificate is `u` padded to `m + 1` bits, `u` recovered as the
first `n` bits — no marker needed, `n` is read off `y`). The verifier language:
`V = {y ++ w : |w| = |y| + 1`, `y` parses as a quadruple
`⟨α, x, 1^n, 1^t⟩`, and the machine `α` denotes accepts `⟨x, w.take n⟩` within
`t` steps`}`. `V ∈ P` by a machine with the named fill obligations: (i)
unique-split recovery — a well-formed input has length `m + (m + 1) = 2m + 1`,
**odd**, so the machine **rejects even lengths** and splits an odd length `N`
at `(N − 1) / 2` (round-1 audit, finding 4, correcting the drafted parity);
(ii) the **quadruple parser** — three nested `pairDecode` passes (the aligned
two-bit grammar; the `UniversalStartup` parsing layer is the in-repo
precedent) plus all-`true` shape checks on the third and fourth components,
rejecting any failure; (iii) **unary-to-binary clock conversion**:
`Turing.timed_universal`'s clock input is `Nat.bits t`, so the verifier
converts the unary `1^t` by counter increments (`Nat.bits 0 = []` at the
`t = 0` edge, where every instance is negative —
`Turing.FinTM.not_computesInTime_zero`); (iv) **assembly and relocated
simulation**: build `pairEncode (pairEncode (Nat.bits t) α) (pairEncode x
(w.take n))` on a work tape and run the timed universal machine `U` of
`Turing.timed_universal c` relocated-and-captured (the standing obligations);
`U` answers `true :: output` or `[false]` by design and its branches are
exhaustive, so acceptance is exactly the complete captured answer
`[true, true]` — a timeout, or any completed output other than `[true]`,
rejects; (v) the verdict with buffered output. **Budget** — where the
hypothesis enters: `U` completes within `C_α·(t+1)^2` steps, and the round-1
audit's inspection of the `Universal` module's bound definitions gives, with
`r = |α|` and `H = c.canonizerTime r`, the chain `C_α ≤ 3r + 14·H + 50` (the
decoded serialization's length `L` bounds the header/state parameters and is
itself at most `H`, the canonizer writing it within its time budget —
`Turing.MultiTapeTM.output_length_le`); `PolyBound c.canonizerTime` then
bounds `C_α` by a polynomial in `r ≤ m` uniformly, and with `t ≤ m` the whole
simulation is polynomial in `m`: `V ∈ P` via `Complexity.mem_P_of_dtime_le`.
**Named fill obligation (new public bridge)**: the public
`Turing.timed_universal` exposes its constant only existentially per code, so
the fill needs a quantitative public form of the bound (an addition to the
audited `Universal` surface, to be requested through the standing shared-file
mechanism and flagged for its audit round — the round-1 finding's repair
guidance; a prose obligation alone cannot discharge the budget). Membership
equivalence: forward, a `TMSAT` witness `u` pads to `m + 1` bits (absorbing
halting keeps the accepting run); backward, a certificate's first `n` bits are
a witness — `Turing.timed_universal`'s two branches convert between `U`'s
answers and `(c.decode α).toFinTM.ComputesInTime (pairEncode x u) [true] t`
exactly, and `Turing.pairEncode_injective` pins the parsed components to the
defining existential's.

**Continuation implementation note.** The exact odd split is P10 at `(1,1)`.
P6 guards each nested parse before extraction; P11 overflow plus whole-word
equality checks both unary fields. The private prefix machine reads exactly
the declared number of witness bits. C1 applies the binary length counter
only to a clock payload while retaining the request, and the canonical §9c
recipe assembles the timed input. Invalid inputs become a valid zero-deadline
request; the proved quantitative bridge, both answer clauses, and the existing
uniform budget close the simulation. Whole-word equality with `[true,true]`
produces the final verdict. -/
theorem TMSAT_mem_NP (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    TMSAT c.toMachineCode ∈ NP := by
  obtain ⟨U, hU⟩ := timed_universal_quantitative c
  obtain ⟨A, d, hbudget⟩ := tmsat_simulation_budget c hc
  have htotal := tmsat_simulator_total c U hU
  have hV : tmsatVerifier c.toMachineCode ∈ P := by
    -- D-MEM closed: guards, exact prefix extraction, valid request assembly,
    -- both simulator outcomes, and whole-answer equality are all checked.
    classical
    obtain ⟨M, C, e, hM⟩ := tmsat_request_poly
    have hs (z : List Bool) : U.ComputesInTime (tmsatRequest z)
        (tmsatResult c.toMachineCode z) (A*(z.length+1)^d) := by
      by_cases hg : tmsatGood z = true
      · obtain ⟨ha,ht⟩ := tmsat_good_bounds z hg
        simpa only [tmsatRequest, tmsatResult, hg, ↓reduceIte] using
          (htotal (tmsatCode z)
            (pairEncode (tmsatInput z) ((tmsatW z).take (tmsatWidth z).length))
            (tmsatClock z).length).mono (hbudget z.length _ _ ha ht)
      · simpa only [tmsatRequest, tmsatResult, if_neg hg, show Nat.bits 0 = [] by simp] using
          (htotal [] [] 0).mono (hbudget z.length 0 0 (by omega) (by omega))
    obtain ⟨N,hN⟩ := FinTM.exists_comp_on_image M U tmsatRequest (tmsatResult c.toMachineCode)
      (fun n => C*(n+1)^e) (fun n => A*(n+1)^d) hM hs
    have hresult : PolyTimeComputable (tmsatResult c.toMachineCode) := by
      refine ⟨N,2*C+A+2,max e d,fun z => (hN z).mono ?_⟩
      have he := Nat.mul_le_mul_left (2*C)
        (Nat.pow_le_pow_right (Nat.succ_pos z.length) (Nat.le_max_left e d))
      have hd := Nat.mul_le_mul_left A
        (Nat.pow_le_pow_right (Nat.succ_pos z.length) (Nat.le_max_right e d))
      have h1 : 1 ≤ (z.length+1)^max e d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      dsimp only
      simp only [Nat.succ_eq_add_one, Nat.mul_assoc] at he hd
      simp only [Nat.add_mul, Nat.mul_assoc]
      omega
    obtain ⟨D,B,b,hD⟩ := (tmsat_pt_eq [true,true]).comp hresult
    apply mem_P_iff.mpr
    refine ⟨B,b,D,fun z => ?_⟩
    have hout : [decide (tmsatResult c.toMachineCode z = [true,true])] =
        [MultiTapeTM.indicator (tmsatVerifier c.toMachineCode : Set (List Bool)) z] := by
      simp only [tmsat_result_accept]
      simp [MultiTapeTM.indicator]
    simpa only [Function.comp_apply, hout] using hD z

  refine ⟨1, 1, tmsatVerifier c.toMachineCode, hV, ?_⟩
  intro y
  simpa only [Nat.pow_one, Nat.one_mul] using tmsat_certificate_equiv c.toMachineCode y

/-- The audited deadline formula majorizes the normalized wrapper runtime.
The certificate length remains exactly `C*(n+1)^c` throughout this inequality.

**Proof sketch.** The paired input plus one cell is bounded by
`(C+3)(n+1)^max(1,c)`. Raise to the wrapper degree, absorb its additive one
into the positive power, and square for the one-work-tape normalization.
Only the deadline is enlarged. -/
private lemma tmsat_deadline_bound (K B e C c n : ℕ) :
    K * (B * (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e + 1) ^ 2 ≤
      ((K + 1) * (B + 1) ^ 2 * (C + 3) ^ (2 * e)) *
        (n + 1) ^ (2 * e * max 1 c) := by
  have hlin : n + 1 ≤ (n + 1) ^ max 1 c := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left 1 c)
  have hpow : (n + 1) ^ c ≤ (n + 1) ^ max 1 c :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right 1 c)
  have hsize : 2 * n + 2 + C * (n + 1) ^ c + 1 ≤
      (C + 3) * (n + 1) ^ max 1 c := by
    have hm := Nat.mul_le_mul_left C hpow
    rw [Nat.add_mul]
    omega
  have hepow : (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e ≤
      (C + 3) ^ e * (n + 1) ^ (e * max 1 c) := by
    calc
      _ ≤ ((C + 3) * (n + 1) ^ max 1 c) ^ e := Nat.pow_le_pow_left hsize e
      _ = _ := by rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm (max 1 c) e]
  have hpos : 1 ≤ (C + 3) ^ e * (n + 1) ^ (e * max 1 c) :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (Nat.succ_pos _))
  have hinner : B * (2 * n + 2 + C * (n + 1) ^ c + 1) ^ e + 1 ≤
      (B + 1) * (C + 3) ^ e * (n + 1) ^ (e * max 1 c) := by
    calc
      _ ≤ B * ((C + 3) ^ e * (n + 1) ^ (e * max 1 c)) +
          (C + 3) ^ e * (n + 1) ^ (e * max 1 c) :=
        Nat.add_le_add (Nat.mul_le_mul_left B hepow) hpos
      _ = _ := by ring
  calc
    _ ≤ (K + 1) * ((B + 1) * (C + 3) ^ e * (n + 1) ^ (e * max 1 c)) ^ 2 :=
      Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_left hinner 2)
    _ = _ := by
      simp only [Nat.mul_pow, ← Nat.pow_mul]
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Constant strings are polynomial-time computable by finite emission chains. -/
private lemma tmsat_constant_poly (w : List Bool) : PolyTimeComputable (fun _ => w) := by
  obtain ⟨M, C, hM⟩ := FinTM.computesFunInTime_const w
  exact ⟨M, C, 1, by simpa only [Nat.pow_one] using hM⟩

/-- The exact binary certificate length is polynomial-time computable,
including zero coefficients and degree zero.

**Proof sketch.** Follow the audited three-way split: coefficient zero emits
the empty word; positive coefficient and degree zero emits its fixed binary
representation from finite control; positive coefficient and positive degree
uses `timeConstructible_poly C (c-1)`. Only the runtime is enlarged. -/
private lemma tmsat_exact_certificate_bits (C c : ℕ) :
    PolyTimeComputable (fun x : List Bool => (C * (x.length + 1) ^ c).bits) := by
  by_cases hC : C = 0
  · simpa [hC] using tmsat_constant_poly []
  · by_cases hc : c = 0
    · simpa [hc] using tmsat_constant_poly C.bits
    · obtain ⟨_, a, _, M, hM⟩ := timeConstructible_poly C (c - 1) (by omega)
      have he : c - 1 + 1 = c := by omega
      simp only [he] at hM
      refine ⟨M, a * (C + 1), c, fun x => (hM x).mono ?_⟩
      have hp : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
      calc
        _ ≤ a * ((C + 1) * (x.length + 1) ^ c) :=
          Nat.mul_le_mul_left a (by rw [Nat.add_mul, Nat.one_mul]; omega)
        _ = _ := by ring

/-- The wrapper's total output function rejects malformed pairs and otherwise
forwards the verifier's verdict on the concatenated components. -/
private noncomputable def tmsatWrapperOutput (V : Language Bool) (z : List Bool) : List Bool :=
  match pairDecode z with
  | none => [false]
  | some (x, u) => [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)]

/-- Three applications of pairing injectivity pin every quadruple component;
unary equality pins the two natural-number fields by taking lengths. -/
private lemma tmsat_quad_injective (α x : List Bool) (n t : ℕ)
    (β y : List Bool) (m s : ℕ) (he : tmsatQuad α x n t = tmsatQuad β y m s) :
    α = β ∧ x = y ∧ n = m ∧ t = s := by
  have h₁ : (α, pairEncode x (pairEncode (List.replicate n true) (List.replicate t true))) =
      (β, pairEncode y (pairEncode (List.replicate m true) (List.replicate s true))) :=
    pairEncode_injective he
  obtain ⟨hα, hrest⟩ := Prod.mk.inj h₁
  have h₂ : (x, pairEncode (List.replicate n true) (List.replicate t true)) =
      (y, pairEncode (List.replicate m true) (List.replicate s true)) :=
    pairEncode_injective hrest
  obtain ⟨hx, hlast⟩ := Prod.mk.inj h₂
  have h₃ : (List.replicate n true, List.replicate t true) =
      (List.replicate m true, List.replicate s true) := pairEncode_injective hlast
  obtain ⟨hn, ht⟩ := Prod.mk.inj h₃
  refine ⟨hα, hx, ?_, ?_⟩
  · simpa only [List.length_replicate] using congrArg List.length hn
  · simpa only [List.length_replicate] using congrArg List.length ht

/-- Given a fixed coded wrapper with the prescribed deadline, the reduction
has exactly the original NP language as its preimage.

**Proof sketch.** Forward, use the original exact-length certificate and the
wrapper's accepting verdict. Backward, nested pairing injectivity forces the
code, input, certificate length, and deadline to be precisely the emitted ones.
Completed-output uniqueness then identifies acceptance with the verifier's
verdict, even if the chosen deadline exceeds the actual halting time. -/
private lemma tmsat_reduction_correct (c : MachineCode) (L V : Language Bool)
    (C e : ℕ) (α : List Bool) (T : ℕ → ℕ)
    (hL : ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ e ∧ x ++ u ∈ V)
    (hM : ∀ x u : List Bool, u.length = C * (x.length + 1) ^ e →
      (c.decode α).toFinTM.ComputesInTime (pairEncode x u)
        [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)] (T x.length)) :
    ∀ x : List Bool, x ∈ L ↔ tmsatQuad α x (C * (x.length + 1) ^ e) (T x.length) ∈ TMSAT c := by
  classical
  intro x
  constructor
  · intro hx
    obtain ⟨u, hu, hv⟩ := (hL x).mp hx
    refine ⟨α, x, u, C * (x.length + 1) ^ e, T x.length, rfl, hu, ?_⟩
    simpa only [MultiTapeTM.indicator, if_pos hv] using hM x u hu
  · rintro ⟨β, y, u, n, t, he, hu, hs⟩
    obtain ⟨rfl, rfl, hn, ht⟩ := tmsat_quad_injective α x
      (C * (x.length + 1) ^ e) (T x.length) β y n t he
    rw [← hn] at hu
    rw [← ht] at hs
    refine (hL _).mpr ⟨u, hu, ?_⟩
    have ho := hs.output_unique (hM _ u hu)
    by_contra hv
    simp [MultiTapeTM.indicator, hv] at ho

/-- Exact unary certificate generation follows the predecessor's three-case
binary-value discipline; the library emits the same value directly.

**Proof sketch.** Coefficient zero emits the empty word. Positive coefficient
and degree zero emits its fixed unary word. Otherwise P5 uses exponent
`c-1+1=c`, whose harvested unary loop parameter is `c-1`. No value is enlarged. -/
private lemma tmsat_certificate_unary (C c : ℕ) :
    PolyTimeComputable (fun x => List.replicate (C*(x.length+1)^c) true) := by
  by_cases hC : C = 0
  · simpa [hC] using polyTimeComputable_const []
  · by_cases hc : c = 0
    · simpa [hc] using polyTimeComputable_const (List.replicate C true)
    · obtain ⟨M,A,hM⟩ := FinTM.computesFunInTime_polyUnary C (c-1+1)
      have he : c-1+1 = c := by omega
      rw [he] at hM
      exact ⟨M,A,c+1,hM⟩

/-- **`TMSAT` is `NP`-hard** [AB09, Theorem 2.9, hardness]: the generic
reduction — for `L ∈ NP`, send `x` to `⟨⌞M⌟, x, 1^{p(|x|)}, 1^{q(m)}⟩`.

**Proof sketch.** Let `L ∈ NP` with parameters `(C₀, c₀, V)` and certificate
length `Q n = C₀·(n+1)^(c₀)`, and, via `Complexity.mem_P_iff`, a machine `M_V`
deciding `V` within `A·(m+1)^d`. **The encoded machine**: a wrapper `M'` that,
on input `z`, parses `z` as `Turing.pairEncode x u` (the pairing parser
obligation; on non-pairs, output `[false]` — `M'` is total), assembles
`x ++ u`, and runs `M_V` relocated-and-captured, forwarding the verdict. `M'`
computes a total function within an explicit polynomial; normalize by the
audited chain `Turing.FinTM.one_work_tape_binary` (its total-function
hypothesis holds) and `Turing.exists_codeTM`, and let `α₀ := c.encode M''` be
the resulting **fixed code string** (this is why plain `Turing.MachineCode`
suffices — the audited `Complexity.HALT_NPHard` recipe). Let
`T' n` the **explicit** deadline formula below. **The reduction map**
`f x := pairEncode α₀ (pairEncode x (pairEncode 1^{Q |x|} 1^{T' |x|}))`.
`Complexity.PolyTimeComputable f` by the named obligations: emit the doubled
fixed string `α₀` from finite control (emission chains), double-and-copy `x`,
and write the two unary runs by binary countdown, under the **exact-value
discipline** of the round-1 audit (finding 3): the certificate length `Q` must
be emitted **exactly** — majorizing it changes the language (at
`C₀ = c₀ = 0` and `L = V = {[true]}`, replacing `Q = 0` by `n + 1` flips the
empty input's membership) — by cases: `C₀ = 0` emits the empty run;
`C₀ > 0, c₀ = 0` emits the fixed constant `C₀` from finite control;
`C₀ > 0, c₀ > 0` computes the exact binary value by
`Complexity.timeConstructible_poly C₀ (c₀ - 1)`. The **deadline may be
majorized** (enlarging `t` only relaxes the budget of a total machine whose
verdict is fixed): with a wrapper bound `B·(s+1)^e` (`B, e ≥ 1`) on inputs of
length `s`, normalization multiplier `K`, and `s = 2n + 2 + Q n` on the
relevant inputs, take the audit's formula — `r := max 1 c₀`,
`D := (K+1)·(B+1)^2·(C₀+3)^(2e)`, `T' n := D·(n+1)^(2er)`; then
`s + 1 ≤ (C₀+3)·(n+1)^r` gives `K·(B·(s+1)^e + 1)^2 ≤ T' n` at every `n`, and
`Complexity.timeConstructible_poly D (2er - 1)` computes `T'`'s exact binary
value (`2er ≥ 1`). Output length: `|f x| = 2|α₀| + 2|x| + 2·Q |x| + T' |x| +
6`, an explicit polynomial. **Correctness**: `f x ∈ TMSAT c` iff — by
`Turing.pairEncode_injective`, which pins the quadruple's components — some
`u` with `|u| = Q n` has `M''.toFinTM.ComputesInTime (pairEncode x u) [true]
(T' n)`; by `M''`'s semantics and budget this holds iff `x ++ u ∈ V` (the
wrapper's verdict is the `V`-indicator, completed outputs are unique —
`Turing.FinTM.ComputesInTime.output_unique`), and the `NP` membership
equivalence for `L` turns "some such `u`" into `x ∈ L`. Conclude
`Complexity.NPHard` by the definition, one reduction per `L ∈ NP`.

**Continuation implementation note.** P6 validity, guarded P13 concatenation,
and W3 implement the total wrapper. Emission uses the proved unary generators
directly, in place of converting the retained exact binary witnesses back by
countdown. The certificate still follows exactly the same three-case table:
zero coefficient, zero degree, and positive coefficient/degree. The deadline
uses the unchanged in-file generator at loop parameter `2er-1` and coefficient
`D`, hence exponent exactly `2er`. The canonical §9c construction retains `x`
and assembles the two exact unary runs; P6 fixed-code pairing supplies the
outermost layer. Neither harvested generator is modified or removed. -/
theorem TMSAT_NPHard (c : MachineCode) : NPHard (TMSAT c) := by
  classical
  intro L hL
  obtain ⟨C₀, c₀, V, hV, hL⟩ := hL
  obtain ⟨A, d, M_V, hM_V⟩ := mem_P_iff.mp hV
  have hwrap : ∃ (W : FinTM Bool) (B e : ℕ), 0 < B ∧ 0 < e ∧
      W.ComputesFunInTime (tmsatWrapperOutput V) (fun s => B * (s + 1) ^ e) := by
    -- D-WRAP closed: guard P13's parse, capture the verifier on the
    -- concatenated components, and reject malformed inputs via W3.
    have hv : PolyTimeComputable
        (fun z => [MultiTapeTM.indicator (V : Set (List Bool)) z]) := ⟨M_V,A,d,hM_V⟩
    have hp := polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid
    have hc : PolyTimeComputable tmsatConcat :=
      polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
    have hw : PolyTimeComputable (tmsatWrapperOutput V) := by
      have h := polyTimeComputable_ite hp (hv.comp hc) (polyTimeComputable_const [false])
      convert h using 1
      funext z
      cases hd : pairDecode z with
      | none => simp [tmsatWrapperOutput, hd]
      | some ab => cases ab; simp [tmsatWrapperOutput, tmsatConcat, hd]
    obtain ⟨W,C,j,hW⟩ := hw
    refine ⟨W,C+1,max 1 j,Nat.succ_pos _,Nat.le_max_left _ _,fun z => (hW z).mono ?_⟩
    exact Nat.mul_le_mul (Nat.le_succ C)
      (Nat.pow_le_pow_right (Nat.succ_pos z.length) (Nat.le_max_right 1 j))

  obtain ⟨W, B, e, hB, he, hW⟩ := hwrap
  obtain ⟨M₁, K, hk, h₁⟩ := FinTM.one_work_tape_binary W (tmsatWrapperOutput V)
    (fun s => B * (s + 1) ^ e) hW
  obtain ⟨M'', hcode⟩ := exists_codeTM M₁ hk
  let α₀ := c.encode M''
  let r := max 1 c₀
  let D := (K + 1) * (B + 1) ^ 2 * (C₀ + 3) ^ (2 * e)
  let T' := fun n => D * (n + 1) ^ (2 * e * r)
  have hD : 0 < D :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos (Nat.succ_pos _)))
      (Nat.pow_pos (by omega))
  have hexp : 1 ≤ 2 * e * r := by
    have hr : 0 < r := Nat.le_max_left 1 c₀
    have her := Nat.mul_pos he hr
    rw [Nat.mul_assoc]
    omega
  have hdeadline : TimeConstructible T' := by
    have h := timeConstructible_poly D (2 * e * r - 1) hD
    have heq : 2 * e * r - 1 + 1 = 2 * e * r := by omega
    simpa only [heq] using h
  have hcertificate := tmsat_exact_certificate_bits C₀ c₀
  have hnormalized (x u : List Bool) (hu : u.length = C₀ * (x.length + 1) ^ c₀) :
      (c.decode α₀).toFinTM.ComputesInTime (pairEncode x u)
        [MultiTapeTM.indicator (V : Set (List Bool)) (x ++ u)] (T' x.length) := by
    have hrun := (hcode (pairEncode x u) (tmsatWrapperOutput V (pairEncode x u)) _).2
      (h₁ (pairEncode x u))
    simp only [tmsatWrapperOutput, pairDecode_pairEncode] at hrun
    rw [show c.decode α₀ = M'' from c.decode_encode M'']
    apply hrun.mono
    simpa only [universal_pair_length, hu] using tmsat_deadline_bound K B e C₀ c₀ x.length
  have hemit : PolyTimeComputable
      (fun x => tmsatQuad α₀ x (C₀ * (x.length + 1) ^ c₀) (T' x.length)) := by
    -- D-EMIT closed: exact unary values are assembled using §9c;
    -- the existing binary witnesses record the same exact values.
    have hq := tmsat_certificate_unary C₀ c₀
    have ht : PolyTimeComputable (fun x => List.replicate (T' x.length) true) := by
      have h := poly_unary_computes (2*e*r-1) D
      have hexact : 2*e*r-1+1 = 2*e*r := by omega
      rw [hexact] at h
      exact ⟨polyUnaryTM (2*e*r-1) D,D+5*(2*e*r)+4,2*e*r,h⟩
    have hinner := polyTimeComputable_id.pairEncode (hq.pairEncode ht)
    have houter := polyTimeComputable_of_linear (FinTM.computesFunInTime_pairEncodeFixed α₀)
    exact houter.comp hinner

  exact ⟨_, hemit, tmsat_reduction_correct c L V C₀ c₀ α₀ T' hL hnormalized⟩

/-- **Theorem 2.9** [AB09]: `TMSAT` is `NP`-complete — over an effective
scheme with a polynomially bounded canonizer, the hypothesis its membership
half requires and cannot drop (round-1 audit, findings 1-2: without it, the
Argument-A scheme's `TMSAT` is `NP`-hard yet outside `NP`, so the completeness
conjunction fails).

**Proof sketch.** `Complexity.TMSAT_mem_NP` (with the same hypothesis `hc`)
and `Complexity.TMSAT_NPHard` at `c.toMachineCode`, assembled by the
definition of `Complexity.NPComplete`. -/
theorem TMSAT_NPComplete (c : EffectiveMachineCode) (hc : PolyBound c.canonizerTime) :
    NPComplete (TMSAT c.toMachineCode) := by
  exact ⟨TMSAT_mem_NP c hc, TMSAT_NPHard c.toMachineCode⟩

end Complexity
