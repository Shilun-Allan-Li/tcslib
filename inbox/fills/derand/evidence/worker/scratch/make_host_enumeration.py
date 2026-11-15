from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
directory = root / 'TCSlib/Complexity/Randomized/SeedMajority'
(directory / 'Enumeration.lean').write_text(r'''/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.SeedMajority.State
import TCSlib.Complexity.Randomized.Build.IterateFind
import TCSlib.Complexity.Randomized.Build.StateLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The finite seed-enumeration machine

Instantiate the generic binary-fuel harvest with a retained-input counting
state. The size guard stays in the total step; it never fires on a genuine
prefix of at most `2^w` rounds. The terminal rank is included in the search.

## Main results

* `Complexity.SeedMajority.exists_countingTM`: a finite machine computes
  the strict seed-majority bit in time `c * 2^w(n) * (n+1)^e`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §7.1, p. 126.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1, step 4.
-/

namespace Complexity.SeedMajority

open Turing

open Classical in
/-- A finite machine computes the seed-majority bit with the claimed time:
`M.ComputesFunInTime (x ↦ [decide (2^(w |x|) < 2 * count_all)])`
`(n ↦ c * (2^(w n) * (n+1)^e))` for some `M,c,e`.
[AB09, §7.1, p. 126]; [PS10, Theorem 180.1, step 4]

**Proof sketch.** Bound the unary width by a polynomial. Then the retained
input and the two counters, including their terminal values, fit in a
fixed polynomial state bound. Induct along the guarded orbit: its rank is
`i`, and its count is `count V x (w |x|) i`. The guard never fires up to the
fuel rank. The terminal test is false before that rank and true there,
so the inclusive first-hit search returns it. Apply the generic-fuel
harvest with the shared binary power-of-two evaluator. The rank bijection
identifies the final prefix count with the count over all seed tuples.
Finally bound the per-round polynomial with `PolyExpr.eval_le` and use
`2^w+2 ≤ 3*2^w` to obtain the required time normal form. -/
theorem exists_countingTM {V : Language Bool} (hV : V ∈ P) (w : ℕ → ℕ)
    (hw : PolyTimeComputable fun x => List.replicate (w x.length) true) :
    ∃ (M : FinTM Bool) (c e : ℕ), M.ComputesFunInTime
      (fun x => [decide (2 ^ w x.length <
        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
          pairEncode x (List.ofFn u) ∈ V).card)])
      (fun n => c * (2 ^ w n * (n + 1) ^ e)) := by
  obtain ⟨C, c, hwidth⟩ := hw.output_length_le
  have hwlen (x : List Bool) : w x.length ≤ C * (x.length + 1) ^ c := by
    simpa only [List.length_replicate] using hwidth x
  let P : PolyExpr := .add (.add (.mul (.const 2) .var)
    (.mul (.const (3 * C)) (.pow (.add .var (.const 1)) c))) (.const 7)
  have hstate (x : List Bool) (i : ℕ) (hi : i ≤ 2 ^ w x.length) :
      (state x i (count V x (w x.length) i)).length ≤ P.eval x.length := by
    have hs := length_state_le x (w x.length) i (count V x (w x.length) i) hi
      (count_le V x (w x.length) i)
    have hwx := hwlen x
    simp only [P, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_pow, PolyExpr.eval_var]
    nlinarith
  have hinit (x : List Bool) : (state x 0 0).length ≤ P.eval x.length := by
    simpa only [count_zero] using hstate x 0 (Nat.zero_le _)
  have horbit (x : List Bool) (i : ℕ) (hi : i ≤ 2 ^ w x.length) :
      (IterateFind.step (advance V w) P x)^[i] (pairEncode x (state x 0 0)) =
        pairEncode x (state x i (count V x (w x.length) i)) := by
    induction i with
    | zero => simp only [Function.iterate_zero_apply, count_zero]
    | succ i ih =>
        rw [Function.iterate_succ_apply', ih (by omega), IterateFind.step_eq,
          pairSndD_pairEncode, advance_state, ← count_succ]
        rw [if_pos (hstate x (i + 1) hi)]
  have hfind (x : List Bool) :
      (List.range (2 ^ w x.length + 1)).find?
        (fun i => finished w (pairSndD
          ((IterateFind.step (advance V w) P x)^[i] (pairEncode x (state x 0 0))))) =
        some (2 ^ w x.length) := by
    apply StateLoop.find?_range_eq_some le_rfl
    · intro i hi
      rw [horbit x i hi.le, pairSndD_pairEncode, finished_state]
      exact decide_eq_false (by omega)
    · rw [horbit x (2 ^ w x.length) le_rfl, pairSndD_pairEncode, finished_state]
      exact decide_eq_true rfl
  obtain ⟨F, aF, dF, hF⟩ :=
    (polyTimeComputable_iff _).mp (polyTimeComputable_seedFuel hw)
  obtain ⟨M, c₀, A, D, hM⟩ := IterateFind.computesFunInTime_find
    (polyTimeComputable_advance hV hw) (polyTimeComputable_finished hw)
    (polyTimeComputable_payload hw) polyTimeComputable_initial (fun n => 2 ^ w n)
    P hinit F aF dF hF
  have hresult : (fun x => match (List.range (2 ^ w x.length + 1)).find?
      (fun i => finished w (pairSndD ((IterateFind.step (advance V w) P x)^[i]
        (pairEncode x (state x 0 0))))) with
      | some i => payload w (pairSndD ((IterateFind.step (advance V w) P x)^[i]
          (pairEncode x (state x 0 0))))
      | none => []) =
      (fun x => [decide (2 ^ w x.length <
        2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
          pairEncode x (List.ofFn u) ∈ V).card)]) := by
    funext x
    rw [hfind, horbit x (2 ^ w x.length) le_rfl, pairSndD_pairEncode,
      payload_state, count_all]
  rw [hresult] at hM
  let Q : PolyExpr := .add (.mul (.const A) (.pow
    (.add (.add (.add (.mul (.const 2) .var) (.const 2)) P) (.const 5)) D)) (.const 1)
  obtain ⟨B, b, hB⟩ := Q.eval_le
  have hbudget (n : ℕ) : A * (2 * n + 2 + P.eval n + 5) ^ D + 1 ≤ B * (n + 1) ^ b := by
    simpa only [Q, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_pow, PolyExpr.eval_var] using hB n
  refine ⟨M, c₀ * B * 3, b, (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_⟩
  apply ((FinTM.computesFunInTime_iff _ _ _).mp hM x).mono
  calc
    c₀ * (A * (2 * x.length + 2 + P.eval x.length + 5) ^ D + 1) *
        (2 ^ w x.length + 2) ≤
        c₀ * (B * (x.length + 1) ^ b) * (3 * 2 ^ w x.length) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c₀ (hbudget x.length))
        (by have hpos := Nat.two_pow_pos (w x.length); omega)
    _ = c₀ * B * 3 * (2 ^ w x.length * (x.length + 1) ^ b) := by ring

end Complexity.SeedMajority
''')
(directory / 'Envelope.lean').write_text(r'''/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A timed computation bounds every work head

The coarse head envelope follows from a completed computation: before its
time bound every head is within that many cells of its initial position;
afterward the halted run is constant. This is the native-initial-configuration
version of the clean-module envelope, stated without a clean seam hypothesis.

## Main results

* `Complexity.SeedMajority.envelope_of_computesInTime`: the all-times head bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §1.2, multitape machines.
-/

namespace Complexity.SeedMajority

open Turing

/-- A finite machine computing `y` on `x` by time `t` keeps each work head
within `t` cells at every time `v`:
`|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ (t : ℤ)`.
[AB09, §1.2]

**Proof sketch.** The published interval bound puts the head within `u`
cells of its start after `u ≤ t` steps, and `Cfg.init_workTapePos` makes the
start zero. For `v > t`, the computation reader says the configuration at
`t` is halted; split the run there and use `runFrom_of_halt`. -/
theorem envelope_of_computesInTime {M : FinTM Bool} {x y : List Bool} {t : ℕ}
    (h : M.ComputesInTime x y t) (v : ℕ) (j : Fin M.k) :
    |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ (t : ℤ) := by
  have bound (u : ℕ) (hu : u ≤ t) :
      |(M.tm.runFrom (M.tm.initCfg x) u).workTapePos j| ≤ (t : ℤ) := by
    have hp := M.tm.workTapePos_runFrom_mem_Icc (M.tm.initCfg x) u j
    rw [Finset.mem_Icc] at hp
    simp only [MultiTapeTM.initCfg_eq, Cfg.init_workTapePos, zero_sub, zero_add] at hp
    have hut : (u : ℤ) ≤ t := by exact_mod_cast hu
    exact abs_le.mpr ⟨by omega, by omega⟩
  by_cases hv : v ≤ t
  · exact bound v hv
  · have hh := ((FinTM.computesInTime_iff M x y t).mp h).1
    have heq : M.tm.runFrom (M.tm.initCfg x) v = M.tm.runFrom (M.tm.initCfg x) t := by
      rw [show v = t + (v - t) by omega, MultiTapeTM.runFrom_add,
        MultiTapeTM.runFrom_of_halt _ hh]
    rw [heq]
    exact bound t le_rfl

end Complexity.SeedMajority
''')
