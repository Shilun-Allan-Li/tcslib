/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionSpec
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.UnaryTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Tseitin emitter machine: transition table and tape walks

The three-work-tape binary Turing machine `BoolCircuit.CktSatReduction.Emitter.emTM`
implementing the Tseitin emitter of `CircuitSatReductionSpec.lean`, and its tape-level
run lemmas.  Work tape `t ∈ {0, 1, 2}` holds counter `t` (the vertex `z`, the arguments
`a`, `b`) in unary (`Turing.UnaryTape.ones`).  The walks over one counter — printing it
(`print_walk`, `back_walk`) and erasing it (`clear_walk`) — are proved here; the
simulation of the abstract run is in `CircuitSatReductionMachine.lean`.

## Main definitions

* `BoolCircuit.CktSatReduction.Emitter.tr` — the transition table.
* `BoolCircuit.CktSatReduction.Emitter.emTM` — the machine.

## Main results

* `BoolCircuit.CktSatReduction.Emitter.print_walk`, `back_walk`, `clear_walk` — the walks
  over one counter.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§1.2: the multi-tape machine; §6.1.2, Lemma 6.11.)
-/

namespace BoolCircuit

namespace CktSatReduction

namespace Emitter

open Turing Turing.UnaryTape

/-! ## The machine -/

/-- The control states: reading the next input symbol in phase `φ` (`rd`); executing
instruction `pc` of the emission program of a gate (`em`); walking left over counter `t`
emitting `1`s (`prW`) and back right (`prB`); walking left erasing counter `t` (`clW`);
starting to erase counter `2` (`clS2`); incrementing the vertex counter (`inc`). -/
inductive St
  | rd (φ : Ph)
  | em (k : GateKind) (c : Fin 3) (pc : Fin 64)
  | prW (k : GateKind) (c : Fin 3) (pc : Fin 64) (t : Fin 3)
  | prB (k : GateKind) (c : Fin 3) (pc : Fin 64) (t : Fin 3)
  | clW (t : Fin 3)
  | clS2
  | inc
  deriving DecidableEq, Fintype

/-- An action on work tape `t` only: input move `im`, optional write `wr` and move `m` on
tape `t`, optional output `o`, next state `q`. -/
def act (t : Fin 3) (im : SignType) (wr : Option (Option Bool)) (m : SignType)
    (o : Option Bool) (q : Option St) : Action 3 Bool St :=
  ⟨im, fun i => if i = t then (wr, m) else (none, 0), o, q⟩

/-- An action touching no work tape. -/
def ctl (im : SignType) (o : Option Bool) (q : Option St) : Action 3 Bool St :=
  ⟨im, fun _ => (none, 0), o, q⟩

/-- The state after counter `t` has been erased: erase counter `2` next, or increment
the vertex counter. -/
def clNext (t : Fin 3) : St := if t = 1 then .clS2 else .inc

/-- **The transition table.** -/
def tr : St → Option Bool → (Fin 3 → Option Bool) → Action 3 Bool St
  | .rd φ, sym, _ => match lstep φ sym with
    | .halt o => ctl 0 o none
    | .go φ' none => ctl .pos none (some (.rd φ'))
    | .go φ' (some t) => act t .pos (some (some true)) .pos none (some (.rd φ'))
    | .gate k c => ctl .pos none (some (.em k c 0))
  | .em k c pc, _, _ => match (prog k c)[pc.val]? with
    | none => act 1 0 none .neg none (some (.clW 1))
    | some (.out b) => ctl 0 (some b) (some (.em k c (pc + 1)))
    | some (.pr t) => act t 0 none .neg none (some (.prW k c pc t))
  | .prW k c pc t, _, w =>
    if (w t).isSome then act t 0 none .neg (some true) (some (.prW k c pc t))
    else act t 0 none .pos none (some (.prB k c pc t))
  | .prB k c pc t, _, w =>
    if (w t).isSome then act t 0 none .pos none (some (.prB k c pc t))
    else ctl 0 none (some (.em k c (pc + 1)))
  | .clW t, _, w =>
    if (w t).isSome then act t 0 (some none) .neg none (some (.clW t))
    else act t 0 none .pos none (some (clNext t))
  | .clS2, _, _ => act 2 0 none .neg none (some (.clW 2))
  | .inc, _, _ => act 0 0 (some (some true)) .pos none (some (.rd .g))

/-- **The Tseitin emitter machine**: three work tapes (the counters), started reading
the number of inputs. -/
def emTM : FinTM Bool where
  k := 3
  State := St
  tm := { q₀ := .rd .n, tr := tr }

/-! ## Tapes and steps -/

/-- One machine step from a running configuration applies the transition. -/
theorem step_some {w : List Bool} (q : St) (p : Fin (w.length + 2))
    (tp : Fin 3 → ℤ → Option Bool) (hd : Fin 3 → ℤ) (out : List Bool) :
    emTM.tm.step (⟨some q, p, tp, hd, out⟩ : Cfg 3 Bool St w) =
      (tr q (Cfg.inputSymbol (⟨some q, p, tp, hd, out⟩ : Cfg 3 Bool St w))
        (fun i => tp i (hd i))).apply ⟨some q, p, tp, hd, out⟩ := rfl

/-- The effect of a one-tape action. -/
theorem apply_act {w : List Bool} {q' : Option St} (t : Fin 3) (im : SignType)
    (wr : Option (Option Bool))
    (m : SignType) (o : Option Bool) (q : Option St) (p : Fin (w.length + 2))
    (tp : Fin 3 → ℤ → Option Bool) (hd : Fin 3 → ℤ) (out : List Bool) :
    (act t im wr m o q).apply (⟨q', p, tp, hd, out⟩ : Cfg 3 Bool St w) =
      ⟨q, moveInputPos p im, Function.update tp t (wrT (tp t) (hd t) wr),
        Function.update hd t (hd t + m), out ++ o.toList⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i = t
    · subst hi; cases wr <;> simp [act, Action.apply, wrT]
    · simp [act, Action.apply, hi]
  · funext i
    by_cases hi : i = t
    · subst hi; simp [act, Action.apply]
    · simp [act, Action.apply, hi]

/-- The effect of a tape-free action. -/
theorem apply_ctl {w : List Bool} {q' : Option St} (im : SignType) (o : Option Bool) (q : Option St)
    (p : Fin (w.length + 2)) (tp : Fin 3 → ℤ → Option Bool) (hd : Fin 3 → ℤ)
    (out : List Bool) :
    (ctl im o q).apply (⟨q', p, tp, hd, out⟩ : Cfg 3 Bool St w) =
      ⟨q, moveInputPos p im, tp, hd, out ++ o.toList⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i; simp [ctl, Action.apply]
  · funext i; simp [ctl, Action.apply]

/-! ## The walks -/

/-- The print walk: in `prW`, from head `j - 1` over a counter of value `m ≥ j`, the
machine emits `j` ones in `j + 1` steps and turns into `prB` at head `0`.

**Proof sketch.** Induction on `j`: at head `-1` the cell is blank and the head steps
right; at head `j - 1 ≥ 0` the cell holds `1`, which is emitted, and the head steps
left. -/
theorem print_walk {w : List Bool} (k : GateKind) (c : Fin 3) (pc : Fin 64) (t : Fin 3)
    (p : Fin (w.length + 2)) (tp : Fin 3 → ℤ → Option Bool) (hd : Fin 3 → ℤ) (m : ℕ)
    (htp : tp t = ones m) :
    ∀ (j : ℕ) (out : List Bool), j ≤ m →
      emTM.tm.runFrom (⟨some (.prW k c pc t), p, tp, Function.update hd t ((j : ℤ) - 1), out⟩ :
        Cfg 3 Bool St w) (j + 1) =
        ⟨some (.prB k c pc t), p, tp, Function.update hd t 0, out ++ List.replicate j true⟩ := by
  intro j
  induction j with
  | zero =>
    intro out _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    have hb : tp t (Function.update hd t ((0 : ℕ) - 1 : ℤ) t) = none := by
      simp [htp, ones_neg]
    simp only [tr, hb, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [apply_act]
    simp [wrT, moveInputPos_zero]
  | succ j ih =>
    intro out hj
    rw [MultiTapeTM.runFrom_succ_eq_step, step_some]
    have hb : tp t (Function.update hd t (((j + 1 : ℕ) : ℤ) - 1) t) = some true := by
      simp only [Function.update_self, htp]
      exact ones_lt (by omega) (by omega)
    simp only [tr, hb, Option.isSome_some, if_true]
    rw [apply_act]
    simp only [wrT, Function.update_eq_self, moveInputPos_zero, Function.update_idem,
      Function.update_self]
    rw [show (((j + 1 : ℕ) : ℤ) - 1 + ((SignType.neg : SignType) : ℤ)) = (j : ℤ) - 1 by
      simp [SignType.cast]; omega]
    rw [ih _ (by omega)]
    simp [List.replicate_succ', ← List.replicate_succ]

/-- The return walk: in `prB`, from head `m - d` over a counter of value `m`, the machine
walks right to the blank cell `m` in `d + 1` steps and resumes the program at the next
instruction.

**Proof sketch.** Induction on `d`: at cell `m` the cell is blank and the program resumes;
at cell `m - d - 1 < m` the cell holds `1` and the head steps right. -/
theorem back_walk {w : List Bool} (k : GateKind) (c : Fin 3) (pc : Fin 64) (t : Fin 3)
    (p : Fin (w.length + 2)) (tp : Fin 3 → ℤ → Option Bool) (hd : Fin 3 → ℤ) (m : ℕ)
    (htp : tp t = ones m) (out : List Bool) :
    ∀ d : ℕ, d ≤ m →
      emTM.tm.runFrom (⟨some (.prB k c pc t), p, tp,
        Function.update hd t (((m - d : ℕ) : ℤ)), out⟩ : Cfg 3 Bool St w) (d + 1) =
        ⟨some (.em k c (pc + 1)), p, tp, Function.update hd t (m : ℤ), out⟩ := by
  intro d
  induction d with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    have hb : tp t (Function.update hd t (((m - 0 : ℕ) : ℤ)) t) = none := by
      simp [htp, ones_ge]
    simp only [tr, hb, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [apply_ctl]
    simp [moveInputPos_zero]
  | succ d ih =>
    intro hd'
    rw [MultiTapeTM.runFrom_succ_eq_step, step_some]
    have hb : tp t (Function.update hd t (((m - (d + 1) : ℕ) : ℤ)) t) = some true := by
      simp only [Function.update_self, htp]
      exact ones_lt (by omega) (by omega)
    simp only [tr, hb, Option.isSome_some, if_true]
    rw [apply_act]
    simp only [wrT, Function.update_eq_self, moveInputPos_zero, Function.update_idem,
      Function.update_self, Option.toList_none, List.append_nil]
    rw [show (((m - (d + 1) : ℕ) : ℤ) + ((SignType.pos : SignType) : ℤ)) =
      (((m - d : ℕ) : ℤ)) by simp [SignType.cast]; omega]
    exact ih (by omega)

/-- The erase walk: in `clW t`, from head `j - 1` over a counter of value `j`, the machine
erases it in `j + 1` steps and moves on (`clNext t`) with the head at `0`.

**Proof sketch.** Induction on `j`: at cell `-1` the cell is blank and the head steps
right; at cell `j - 1` the cell holds `1`, which is erased (leaving the unary tape of
`j - 1`, `update_ones_pred`), and the head steps left. -/
theorem clear_walk {w : List Bool} (t : Fin 3) (p : Fin (w.length + 2))
    (tp : Fin 3 → ℤ → Option Bool) (hd : Fin 3 → ℤ) (out : List Bool) :
    ∀ j : ℕ,
      emTM.tm.runFrom (⟨some (.clW t), p, Function.update tp t (ones j),
        Function.update hd t ((j : ℤ) - 1), out⟩ : Cfg 3 Bool St w) (j + 1) =
        ⟨some (clNext t), p, Function.update tp t (ones 0), Function.update hd t 0, out⟩ := by
  intro j
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, step_some]
    have hb : Function.update tp t (ones 0) t (Function.update hd t ((0 : ℕ) - 1 : ℤ) t) =
        none := by
      simp [ones_neg]
    simp only [tr, hb, Option.isSome_none, Bool.false_eq_true, if_false]
    rw [apply_act]
    simp [wrT, moveInputPos_zero]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step, step_some]
    have hb : Function.update tp t (ones (j + 1)) t
        (Function.update hd t (((j + 1 : ℕ) : ℤ) - 1) t) = some true := by
      simp only [Function.update_self]
      exact ones_lt (by omega) (by omega)
    simp only [tr, hb, Option.isSome_some, if_true]
    rw [apply_act]
    simp only [wrT, Function.update_self, moveInputPos_zero, Function.update_idem,
      Option.toList_none, List.append_nil]
    rw [show (((j + 1 : ℕ) : ℤ) - 1) = ((j : ℕ) : ℤ) by omega, update_ones_pred,
      show ((j : ℕ) : ℤ) + ((SignType.neg : SignType) : ℤ) = (j : ℤ) - 1 by
        simp [SignType.cast]; omega]
    exact ih

end Emitter

end CktSatReduction

end BoolCircuit
