/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Catalog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: the routine instance

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`).
R3 clear as a contract, with its frame (MIG-0a, moved here from `Build/Contract.lean` as landed on
2026-10-13 with no statement changed) and its joint trajectory (MIG-0b). MIG-11's instances of the
framed rows join it.

## Main definitions

* `Turing.clearTM_contract`: R3 clear as a contract.

## Main results

* `Turing.clearTM_contract_frames`, `Turing.clearTM_contract_traj`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the framing adapted as `Turing.Contract.Frames` (design adaptation; full entry in
  `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **R3 clear as a contract** (the fit test, from `Turing.clearTM_run_ofCfg`): the index is the
stored word `w`. Started in the sweep phase with `w`, delimited, at the head of tape `i`, the
routine reaches `done` in exactly `2|w| + 2` steps, and not earlier, with the cells
`[pos, pos + |w|)` of tape `i` blank and every other field unchanged; through the endpoint the
head of tape `i` stays in `[pos - 1, pos + |w|]` and every other head is fixed.

**Proof sketch.** Each field is the corresponding clause of `Turing.clearTM_run_ofCfg`; a fixed
head lies in its one-point interval. -/
def clearTM_contract (i : Fin k) (x : List Γ) :
    Contract (clearTM k i) SweepPhase.sweep {some SweepPhase.done} (List Γ) x where
  pre w d := ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
    d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape w p
  time w _ := 2 * w.length + 2
  post w d :=
    { d with
      state := some SweepPhase.done
      workTapes := fun j q =>
        if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then none
        else d.workTapes j q }
  lo w d j := if j = i then d.workTapePos j - 1 else d.workTapePos j
  hi w d j := if j = i then d.workTapePos j + w.length else d.workTapePos j
  run w d hd hp := (clearTM_run_ofCfg i w d hd hp).1
  exit_mem _ _ _ _ := Set.mem_singleton _
  cut w d hd hp u hu h := (clearTM_run_ofCfg i w d hd hp).2.1 u hu (Set.mem_singleton_iff.mp h)
  env w d hd hp u hu j := by
    have h := (clearTM_run_ofCfg i w d hd hp).2.2 j u hu
    by_cases hj : j = i
    · subst hj
      simpa using h
    · simp only [hj, if_false] at h ⊢
      rw [h]
      exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

/-- R3 clear frames the cleared word's cells on its tape, and nothing else: its footprint is
`[pos, pos + |w|)` on tape `i` and empty on every other tape.

**Proof sketch.** The endpoint blanks a cell only when the cell lies in the footprint; any other
cell takes the `else` branch of its definition, which is the start's cell. -/
theorem clearTM_contract_frames (i : Fin k) (x : List Γ) :
    (clearTM_contract i x).Frames fun w d j =>
      if j = i then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length) else ∅ := by
  intro w d _ _ j q hq
  show (if j = i ∧ d.workTapePos j ≤ q ∧ q < d.workTapePos j + (w.length : ℤ) then none
      else d.workTapes j q) = d.workTapes j q
  rw [if_neg]
  rintro ⟨rfl, h₁, h₂⟩
  apply hq
  show q ∈ if j = j then Set.Ico (d.workTapePos j) (d.workTapePos j + w.length) else ∅
  rw [if_pos rfl]
  exact ⟨h₁, h₂⟩

/-- **A joint trajectory of R3 clear** (an instance): every head other than the cleared tape's
stays at its start, a relation on the whole head vector. -/
theorem clearTM_contract_traj (i : Fin k) (x : List Γ) :
    (clearTM_contract i x).Traj fun _ d p => ∀ j, j ≠ i → p j = d.workTapePos j := by
  intro w d hd hp u hu j hj
  have h := (clearTM_contract i x).env w d hd hp u hu j
  have hlo : (clearTM_contract i x).lo w d j = d.workTapePos j := if_neg hj
  have hhi : (clearTM_contract i x).hi w d j = d.workTapePos j := if_neg hj
  rw [hlo, hhi, Finset.mem_Icc] at h
  exact le_antisymm h.2 h.1

end Turing
