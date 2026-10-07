/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Robustness.ObliviousSetup

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious machines: the halting ledger

This file closes the quadratic cost accounting for the length-only schedule:
the arithmetic ledger `obliviousLedger_bound` combines the clock-capture,
initialization, and macrostep costs proved in the previous modules into a
uniform quadratic halting bound for the schedule (`obliviousSchedule_halts`)
and hence for the candidate machine (`obliviousCandidate_halts`). It also
provides the decorated-configuration bridge `decoratedCfg` with its
initialization and step laws, used by the data-machine correctness proof in
`Robustness/Oblivious.lean`. It was split out mechanically from
`Robustness/Oblivious.lean` at the epoch-3→4 merge; provenance: epoch-3 fill,
batch C.

## Main results

* `Complexity.obliviousSchedule_halts` — the schedule halts within a uniform
  quadratic bound.
* `Complexity.obliviousCandidate_halts` — the candidate halts within the same
  bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Remark 1.7, Exercise 1.5.)
-/

namespace Complexity

open Turing

/-- Arithmetic bound for the schedule's operational ledger. The clock,
initialization, and macrostep run identities above supply its individual costs.
The data-output correctness proof is a separate invariant. -/
private lemma obliviousLedger_bound (a b u n τ width : ℕ)
    (hn : n ≤ u) (hτ : τ ≤ b * (u + 1)) (hw : width ≤ b * (u + 1)) :
    τ + 3 * n + 18 + (u + 1) * (2 * width + (a + 1) + 4) +
        22 * ((a + 1) * (u + 1)) + 18 * ((a + 1) * (u + 1)) ^ 2 ≤
      (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (u + 1) ^ 2 := by
  have hv : u + 1 ≤ (u + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hv1 : 1 ≤ (u + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  have ht : τ ≤ b * (u + 1) ^ 2 := hτ.trans (Nat.mul_le_mul_left _ hv)
  have hthree : 3 * n ≤ 3 * (u + 1) ^ 2 :=
    Nat.mul_le_mul_left _ ((hn.trans (Nat.le_succ _)).trans hv)
  have hconst : 18 ≤ 18 * (u + 1) ^ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 18 hv1
  have hcounter : (u + 1) * (2 * width + (a + 1) + 4) ≤
      2 * b * (u + 1) ^ 2 + ((a + 1) + 4) * (u + 1) ^ 2 := by
    calc
      _ ≤ (u + 1) * (2 * (b * (u + 1)) + (a + 1) + 4) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 2 * b * (u + 1) ^ 2 + ((a + 1) + 4) * (u + 1) := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hv) _
  have hsetup : 22 * ((a + 1) * (u + 1)) ≤ 22 * (a + 1) * (u + 1) ^ 2 := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hv
  have he : (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (u + 1) ^ 2 =
      b * (u + 1) ^ 2 + 3 * (u + 1) ^ 2 + 18 * (u + 1) ^ 2 +
      (2 * b * (u + 1) ^ 2 + ((a + 1) + 4) * (u + 1) ^ 2) +
      22 * (a + 1) * (u + 1) ^ 2 + 18 * ((a + 1) * (u + 1)) ^ 2 := by ring
  rw [he]
  omega

/-- The concrete schedule halts within a uniform quadratic bound. This theorem
includes clock capture, arbitrary input reset, copying, fixed-width budget
conversion, full guide allocation, all macrosteps, and the final counter test.
The decorated answer-bit invariant is proved separately below. -/
private lemma obliviousSchedule_halts (W : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (x : List Bool) :
    ∃ t ≤ (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (T x.length + 1) ^ 2,
      ((obliviousSchedule W a).tm.runFrom
        ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) t).state = none := by
  obtain ⟨τ, hτ, c, hs, ho, hclock⟩ := clockStageCfg_captures W a b T hW x
  have hv : budgetValue c.output = T x.length := by rw [ho, budgetValue_bits]
  have hn : (x.map oblEmbed).length + 1 ≤ (a + 1) * (T x.length + 1) := by
    simp only [List.length_map]
    calc
      x.length + 1 ≤ T x.length + 1 := Nat.add_le_add_right (hT x.length) 1
      _ = 1 * (T x.length + 1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨w', hlen, hinit⟩ := setupCfg_initializes W a (clockStageCfg W a c)
    (clockStageCfg W a c).inputPos c.output (T x.length) hv hn
  rw [← clockStageCfg_setup W a c hs] at hinit
  let B := (a + 1) * (T x.length + 1)
  let initTime := ((clockStageCfg W a c).inputPos.val - 1 + 2) +
    ((2 * (x.map oblEmbed).length + 4) +
      ((T x.length + 1) * (2 * c.output.length + (a + 1) + 4) + (14 * B + 10)))
  let finishTime := B * (6 * (3 * B) + 8) + 1
  let t := (τ + 1) + (initTime + finishTime)
  refine ⟨t, ?_, ?_⟩
  · have hwidth : c.output.length ≤ b * (T x.length + 1) := by
      have hw := (FinTM.computesInTime_iff W _ _ _).mp (hW x)
      have hl := MultiTapeTM.output_length_le W.tm x (b * (T x.length + 1))
      rw [hw.2] at hl
      simpa only [ho] using hl
    have hp : (clockStageCfg W a c).inputPos.val - 1 ≤ x.length := by
      have hh := c.inputPos.isLt
      change c.inputPos.val - 1 ≤ x.length
      omega
    have ht : t = τ + ((clockStageCfg W a c).inputPos.val - 1) + 2 * x.length + 18 +
        (T x.length + 1) * (2 * c.output.length + (a + 1) + 4) + 22 * B + 18 * B ^ 2 := by
      dsimp only [t, initTime, finishTime]
      simp only [List.length_map]
      ring
    rw [ht]
    apply le_trans _ (obliviousLedger_bound a b (T x.length) x.length τ c.output.length
      (hT x.length) hτ hwidth)
    dsimp only [B]
    omega
  · change ((obliviousSchedule W a).tm.runFrom
        ((obliviousSchedule W a).tm.initCfg (x.map oblEmbed)) ((τ + 1) + (initTime + finishTime))).state = none
    rw [MultiTapeTM.runFrom_add, hclock, MultiTapeTM.runFrom_add, hinit]
    have hf := setupCfg_finish W a (clockStageCfg W a c)
      ⟨(x.map oblEmbed).length + 1, by omega⟩ (c.output.length + 1) (clockTape w') B
    rw [hf]
    rfl

/-- The exact binary coding and schedule decoration preserve the schedule's
quadratic halting bound. Source-dependent data cannot stop or prolong this run. -/
lemma obliviousCandidate_halts (W M : FinTM Bool) (a b : ℕ) (T : ℕ → ℕ)
    (hW : ∀ x, W.ComputesInTime x (T x.length).bits (b * (T x.length + 1)))
    (hT : ∀ n, n ≤ T n) (x : List Bool) :
    ∃ t ≤ (18 * (a + 1) ^ 2 + 23 * (a + 1) + 3 * b + 25) * (T x.length + 1) ^ 2,
      ((obliviousCandidate W M a).tm.runFrom ((obliviousCandidate W M a).tm.initCfg x) t).state = none := by
  classical
  obtain ⟨t, ht, hs⟩ := obliviousSchedule_halts W a b T hW hT x
  refine ⟨t, ht, ?_⟩
  unfold obliviousCandidate
  rw [parallelTM_run]
  have h := congrArg Cfg.state (decorateTM_run (obliviousSchedule W a) (M.k + 1)
    (Fin.natAdd W.k (2 : Fin 3)) (obliviousDataInit M) (obliviousVisit W M a)
    (obliviousSchedule_output W a) (x.map oblEmbed) t)
  rw [hs] at h
  change Option.map Prod.fst _ = none at h
  change _ = none
  exact Option.map_eq_none_iff.mp h

/-- Extend an arbitrary schedule configuration by aligned data tapes and
finite registers. The output is maintained separately from the silent schedule. -/
def decoratedCfg {A S D : Type} {k l : ℕ} {x : List A} (head : Fin k)
    (c : Cfg k A S x) (d : D) (tapes : Fin l → ℤ → Option A) (out : List A) :
    Cfg (k + l) A (S × D) x :=
  ⟨c.state.map (fun q => (q, d)), c.inputPos, Fin.addCases c.workTapes tapes,
    Fin.addCases c.workTapePos (fun _ => c.workTapePos head), out⟩

/-- The extra data tapes begin blank and aligned with the schedule's origin. -/
lemma decoratedCfg_init {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A) (x : List A) :
    (decorateTM P l head initial visit).tm.initCfg x =
      decoratedCfg head (P.tm.initCfg x) initial (fun _ _ => none) [] := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i z
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [decoratedCfg]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [decoratedCfg]
  · rfl

/-- One decorated transition consists of exactly the prescribed schedule step
and the local data visit. This identity exposes data writes without changing
the already proved physical trajectory or timing. -/
lemma decoratedCfg_step {A D : Type} [Fintype D] [DecidableEq D]
    (P : FinTM A) (l : ℕ) (head : Fin P.k) (initial : D)
    (visit : P.State → D → Option A → (Fin P.k → Option A) →
      (Fin l → Option A) → D × (Fin l → Option (Option A)) × Option A)
    {x : List A} (c : Cfg P.k A P.State x) (q : P.State) (hs : c.state = some q)
    (d : D) (tapes : Fin l → ℤ → Option A) (out : List A) :
    let v := visit q d c.inputSymbol c.workTapeSymbols (fun i => tapes i (c.workTapePos head))
    (decorateTM P l head initial visit).tm.step (decoratedCfg head c d tapes out) =
      decoratedCfg head (P.tm.step c) v.1
        (fun i => setupWrite (tapes i) (c.workTapePos head) (v.2.1 i)) (out ++ v.2.2.toList) := by
  dsimp only
  have hstate : (decoratedCfg head c d tapes out).state = some (q, d) := by
    simp only [decoratedCfg, hs, Option.map_some]
  have hi : (decoratedCfg head c d tapes out).inputSymbol = c.inputSymbol := rfl
  have hl : (fun i => (decoratedCfg head c d tapes out).workTapeSymbols (i.castAdd l)) =
      c.workTapeSymbols := by
    funext i
    simp only [decoratedCfg, Cfg.workTapeSymbols, Fin.addCases_left]
  have hr : (fun i => (decoratedCfg head c d tapes out).workTapeSymbols (i.natAdd P.k)) =
      fun i => tapes i (c.workTapePos head) := by
    funext i
    simp only [decoratedCfg, Cfg.workTapeSymbols, Fin.addCases_right]
  unfold MultiTapeTM.step
  rw [hstate, hs]
  dsimp only [decorateTM]
  rw [hi, hl, hr]
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [decoratedCfg, Action.apply, Fin.addCases_left]
    · simp only [decoratedCfg, Action.apply, Fin.addCases_right, setupWrite]
      rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [decoratedCfg, Action.apply, Fin.addCases_left]
    · simp only [decoratedCfg, Action.apply, Fin.addCases_right]
  · rfl

end Complexity
