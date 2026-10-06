/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Algebra.BigOperators.Fin
import TCSlib.Complexity.SpaceComplexity.Machines.Call

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correctness of the compiled machine

The semantics of a register-tape program (`Complexity.LogProg.rstep`): ordinary nodes take
their machine step, a call node asks an oracle about the virtual input of the call
(`Complexity.LogProg.vword` of `Complexity.LogProg.callSegs`) and continues in its `yes` or
`no` state with the input head back on the first cell. If the deciders answer the oracle
cleanly, the compiled machine (`Complexity.LogProg.compileTM`) computes what the program
computes (`Complexity.LogProg.compile_correct`), in space bounded by the program's register
ranges plus the deciders' space (`Complexity.LogProg.compile_space`).

## Main definitions

* `Complexity.LogProg.tapeWord` — the word stored on a register tape.
* `Complexity.LogProg.rstep` — one step of a program, calls being atomic oracle questions.
* `Complexity.LogProg.CallsOK` — the preconditions of every call along a run.
* `Complexity.LogProg.compileFinTM` — the compiled machine as a bundled finite machine.

## Main results

* `Complexity.LogProg.compile_correct` — the compiled machine halts with the program's
  output, all heads in the given ranges at all times.
* `Complexity.LogProg.compile_space` — its space usage is at most the sum of the register
  ranges plus `kD (2B + 1)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- The word stored on a register tape (from cell `0`; `[]` if the tape is not of this
shape). -/
noncomputable def tapeWord (f : ℤ → Option Bool) : List Bool :=
  open Classical in if h : ∃ w, f = FinTM.bufferTape w then h.choose else []

/-- A stored word is read back. -/
lemma tapeWord_bufferTape (w : List Bool) : tapeWord (FinTM.bufferTape w) = w := by
  have h : ∃ w', FinTM.bufferTape w = FinTM.bufferTape w' := ⟨w, rfl⟩
  unfold tapeWord
  rw [dif_pos h]
  have hspec := h.choose_spec
  -- `bufferTape` is injective
  apply List.ext_getElem?
  intro i
  have := congrFun hspec (i : ℤ)
  simpa [FinTM.bufferTape] using this.symm

/-- The register words of a program configuration. -/
noncomputable def regWords (c : Cfg m Bool Λ x) (r : Fin m) : List Bool := tapeWord (c.workTapes r)

/-- **One step of a register-tape program**: an ordinary node takes its machine step; a call
node asks `oracle` (decider `cs.dec`) about its virtual input and moves to `yes` or `no`,
with the input head on the first cell. -/
noncomputable def rstep (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool)
    (c : Cfg m Bool Λ x) : Cfg m Bool Λ x :=
  match c.state with
  | none => c
  | some l =>
    match P.call l with
    | none => P.tm.step c
    | some cs =>
      { c with
        state := some (if oracle cs.dec (vword (callSegs cs x (regWords c))) then cs.yes
          else cs.no),
        inputPos := 1 }

/-- The program run: `n` steps of `rstep`. -/
noncomputable def rrun (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool)
    (c : Cfg m Bool Λ x) (n : ℕ) : Cfg m Bool Λ x :=
  (rstep P oracle)^[n] c

/-- Running a register-tape program `n + 1` steps is one more step after `n` steps. -/
lemma rrun_succ (P : RProg m d Λ) (oracle : Fin d → List Bool → Bool) (c : Cfg m Bool Λ x)
    (n : ℕ) : rrun P oracle c (n + 1) = rstep P oracle (rrun P oracle c n) := by
  simp [rrun, Function.iterate_succ_apply']

/-- The preconditions of a call at configuration `c` (if `c` is at a call node): distinct
argument registers holding words with their heads at the origin and within the register
ranges, input head on the first cell, and a decider answering the oracle cleanly within head
range `B`. -/
def CallOK (P : RProg m d Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B : ℕ) (c : Cfg m Bool Λ x) :
    Prop :=
  ∀ l cs, c.state = some l → P.call l = some cs →
    cs.args.Nodup ∧ c.inputPos.val = 1 ∧
    (∀ r ∈ cs.args, c.workTapes r = FinTM.bufferTape (regWords c r) ∧ c.workTapePos r = 0 ∧
      lo r ≤ -1 ∧ ((regWords c r).length : ℤ) ≤ hi r) ∧
    CleanRun D (q0 cs.dec) (vword (callSegs cs x (regWords c)))
      (oracle cs.dec (vword (callSegs cs x (regWords c)))) B

/-- **Correctness of the compiled machine.** If the program halts after `N` steps with
output `w`, its register heads stay in `[lo r, hi r]`, and every call along the way meets
its preconditions, then the compiled machine halts with output `w`, and at every time its
register heads are in `[lo r, hi r]` and its decider heads in `[-B, B]`.

**Proof sketch.** Induction on the program run, keeping the compiled machine on the seam
(`Complexity.LogProg.seam`) of the program configuration: ordinary steps are simulated in
lockstep (`step_seam_prog`), calls by `call_run`. -/
theorem compile_correct (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B : ℕ)
    (N : ℕ)
    (hbox : ∀ t ≤ N, ∀ r, lo r ≤ (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ∧
      (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ≤ hi r)
    (hcalls : ∀ t < N, CallOK P D q0 oracle lo hi B (rrun P oracle (Cfg.init l₀ x) t)) :
    ∃ T, (compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T =
        seam (rrun P oracle (Cfg.init l₀ x) N) ∧
      ∀ t ≤ T, (∀ r, lo r ≤ ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x)
          t).workTapePos (Fin.castAdd kD r) ∧
          ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) t).workTapePos
            (Fin.castAdd kD r) ≤ hi r) ∧
        ∀ i, |((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) t).workTapePos
          (Fin.natAdd m i)| ≤ B := by
  induction N with
  | zero =>
    refine ⟨0, by rw [MultiTapeTM.runFrom_zero, seam_init]; rfl, fun t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    refine ⟨fun r => ?_, fun i => ?_⟩
    · have := hbox 0 le_rfl r
      simpa [seam_init, seam, rrun] using this
    · simp
  | succ N ih =>
    obtain ⟨T, hT, hTb⟩ := ih (fun t ht => hbox t (by omega)) (fun t ht => hcalls t (by omega))
    set c := rrun P oracle (Cfg.init l₀ x) N with hc
    have hbN := hbox N (by omega)
    have hbN1 := hbox (N + 1) le_rfl
    rw [rrun_succ, ← hc] at hbN1 ⊢
    -- one program step from `c`
    have hstep : ∃ T', (compileTM P l₀ D q0).runFrom (seam c) T' = seam (rstep P oracle c) ∧
        ∀ t ≤ T', (∀ r, lo r ≤ ((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos
            (Fin.castAdd kD r) ∧ ((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos
              (Fin.castAdd kD r) ≤ hi r) ∧
          ∀ i, |((compileTM P l₀ D q0).runFrom (seam c) t).workTapePos (Fin.natAdd m i)| ≤ B := by
      cases hs : c.state with
      | none =>
        refine ⟨0, by simp [rstep, hs], fun t ht => ?_⟩
        obtain rfl : t = 0 := by omega
        exact ⟨fun r => by simpa [seam] using hbN r, fun i => by simp [seam]⟩
      | some l =>
        cases hcl : P.call l with
        | none =>
          have hst := step_seam_prog P l₀ D q0 c l hs hcl
          have hr : rstep P oracle c = P.tm.step c := by simp [rstep, hs, hcl]
          refine ⟨1, by rw [hr]; exact hst, fun t ht => ?_⟩
          rcases Nat.lt_or_ge t 1 with h | h
          · obtain rfl : t = 0 := by omega
            exact ⟨fun r => by simpa [seam] using hbN r, fun i => by simp [seam]⟩
          · obtain rfl : t = 1 := by omega
            rw [show (compileTM P l₀ D q0).runFrom (seam c) 1 =
              (compileTM P l₀ D q0).step (seam c) from rfl, hst, ← hr]
            exact ⟨fun r => by simpa [seam] using hbN1 r, fun i => by simp [seam]⟩
        | some cs =>
          obtain ⟨hnd, hin, hargs, hclean⟩ := hcalls N (by omega) l cs hs hcl
          obtain ⟨T', hb', hr'⟩ := call_run P l₀ D q0 hs hcl (fun r hr => (hargs r hr).1)
            (fun r hr => (hargs r hr).2.1) hnd hin _ B hclean
          have hr : rstep P oracle c = { c with
              state := some (if oracle cs.dec (vword (callSegs cs x (regWords c))) then cs.yes
                else cs.no), inputPos := 1 } := by simp [rstep, hs, hcl]
          refine ⟨T', by rw [hr]; exact hr', fun t ht => ⟨fun r => ?_, (hb' t ht).2⟩⟩
          obtain ⟨h1, h2⟩ := (hb' t ht).1 r
          beta_reduce at h1 h2
          by_cases hrm : r ∈ cs.args
          · obtain ⟨-, -, hlo, hhi⟩ := hargs r hrm
            have := h2 hrm
            constructor <;> omega
          · rw [h1 hrm]; exact hbN r
    obtain ⟨T', hT', hTb'⟩ := hstep
    refine ⟨T + T', by rw [MultiTapeTM.runFrom_add, hT, hT'], ?_⟩
    apply runFrom_forall_append (Q := fun g =>
      (∀ r, lo r ≤ g.workTapePos (Fin.castAdd kD r) ∧ g.workTapePos (Fin.castAdd kD r) ≤ hi r) ∧
        ∀ i, |g.workTapePos (Fin.natAdd m i)| ≤ B) hTb
    rw [hT]
    exact hTb'

/-- The space used up to time `T` is bounded by the sizes of ranges containing every head
at every time up to `T`. -/
lemma spaceUsed_le_of_ranges {K : ℕ} {S : Type} (tm : MultiTapeTM K Bool S)
    (c : Cfg K Bool S x) (T : ℕ) (lo hi : Fin K → ℤ)
    (h : ∀ t ≤ T, ∀ i, lo i ≤ (tm.runFrom c t).workTapePos i ∧
      (tm.runFrom c t).workTapePos i ≤ hi i) :
    tm.spaceUsed c T ≤ ∑ i, (hi i - lo i + 1).toNat := by
  unfold MultiTapeTM.spaceUsed MultiTapeTM.spaceUsedByTape
  refine Finset.sum_le_sum fun i _ => ?_
  have hsub : tm.visitedByTapeHead c T i ⊆ Finset.Icc (lo i) (hi i) := by
    intro z hz
    simp only [MultiTapeTM.visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Finset.mem_Icc]
    exact h t (by omega) i
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Int.card_Icc]
  congr 1
  ring

/-- The compiled machine as a bundled finite machine. -/
def compileFinTM [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) : FinTM Bool where
  k := m + kD
  State := CSt Λ SD m
  tm := compileTM P l₀ D q0

/-- **The compiled machine computes what the program computes, in the program's space plus
the deciders' space**: if the program halts after `N` steps with output `w`, register heads
in `[lo r, hi r]`, and all calls meet their preconditions with decider head range `B`, then
the compiled machine halts on `x` with output `w`, having visited at most
`∑ r (hi r - lo r + 1) + kD (2B + 1)` work cells.

**Proof sketch.** `compile_correct` gives the halting time and the head ranges;
`spaceUsed_le_of_ranges` turns ranges into space, the register tapes and the decider tapes
being the two blocks of `Fin (m + kD)`. -/
theorem compile_space [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (oracle : Fin d → List Bool → Bool) (lo hi : Fin m → ℤ) (B N : ℕ) (w : List Bool)
    (hhalt : (rrun P oracle (Cfg.init l₀ x) N).state = none)
    (hout : (rrun P oracle (Cfg.init l₀ x) N).output = w)
    (hbox : ∀ t ≤ N, ∀ r, lo r ≤ (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ∧
      (rrun P oracle (Cfg.init l₀ x) t).workTapePos r ≤ hi r)
    (hcalls : ∀ t < N, CallOK P D q0 oracle lo hi B (rrun P oracle (Cfg.init l₀ x) t)) :
    ∃ T, (compileFinTM P l₀ D q0).ComputesInTime x w T ∧
      (compileFinTM P l₀ D q0).tm.spaceUsed ((compileFinTM P l₀ D q0).tm.initCfg x) T ≤
        ∑ r, (hi r - lo r + 1).toNat + kD * (2 * B + 1) := by
  obtain ⟨T, hT, hTb⟩ := compile_correct P l₀ D q0 oracle lo hi B N hbox hcalls
  refine ⟨T, ?_, ?_⟩
  · rw [FinTM.computesInTime_iff]
    change ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T).state = none ∧
      ((compileTM P l₀ D q0).runFrom ((compileTM P l₀ D q0).initCfg x) T).output = w
    rw [hT]
    exact ⟨by show Option.map _ _ = none; rw [hhalt]; rfl, by show _ = w; exact hout⟩
  · change (compileTM P l₀ D q0).spaceUsed ((compileTM P l₀ D q0).initCfg x) T ≤ _
    have := spaceUsed_le_of_ranges (compileTM P l₀ D q0) ((compileTM P l₀ D q0).initCfg x) T
      (Fin.append lo (fun _ => -(B : ℤ))) (Fin.append hi (fun _ => (B : ℤ))) (by
        intro t ht i
        refine Fin.addCases (fun r => ?_) (fun j => ?_) i
        · simpa using (hTb t ht).1 r
        · have := (hTb t ht).2 j
          simp only [Fin.append_right]
          rw [abs_le] at this
          exact this)
    refine this.trans (le_of_eq ?_)
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    congr 1
    congr 1
    omega

end Complexity.LogProg
