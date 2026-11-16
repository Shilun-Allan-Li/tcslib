/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedFields
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
            (false && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Present and absent argument cases for the two-step gate clock

A step below twice the gate count either names an actual argument at its
current gate or has exactly unchanged stage labels. Missing arguments use
the existing arity-zero/arity-at-most-one equations without selecting a
fictional wire. No new semantic object or probability result is introduced.

## Main definitions

None.

## Main results

* `step_cases_exact`: the present argument has gate index `t/2` and position `t%2`.
* `step_cases`: a shorter equality-or-present-argument interface.

`SelectedFields.sample_eq_of_stageBit_eq` already transports the equality
branch through the complete encoded sample; this module reuses that interface.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (the gate-by-gate hybrid with two substeps).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases

open BoolCircuit

variable {inputs : ℕ} (C : DAGCircuit inputs) (v : ℕ → Bool)
  (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
  (hconsistency : ∀ i : Fin C.gates.length,
    gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (inputs + i))

include hA hconsistency

/-- Every clock step `t < 2*gatecount` either leaves the stage-label family
unchanged or names an actual argument at gate `t/2` and position `t%2`.
No selected wire is required in the missing-argument branch. [PS10, Theorem 163.7]

**Proof sketch.** Division by two identifies the current gate and the remainder
identifies its first or second position. If that position is in range, return
its finite index. Otherwise remainder zero forces arity zero, where the first
substep changes nothing. Remainder one forces arity at most one, where the
consistent all-zero-row argument makes the second substep unchanged. -/
theorem step_cases_exact (t : ℕ) (ht : t < 2 * C.gates.length) :
    GateHybrids.stageBit C v t = GateHybrids.stageBit C v (t + 1) ∨
      ∃ i : Fin C.gates.length, ∃ p : Fin (C.gates[i.val]).args.length,
        i.val = t / 2 ∧ p.val = t % 2 ∧ t = 2 * i.val + p.val ∧ p.val < 2 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin C.gates.length, i.val = t / 2 :=
    ⟨⟨t / 2, by omega⟩, rfl⟩
  by_cases hp : t % 2 < (C.gates[i.val]).args.length
  · right
    refine ⟨i, ⟨t % 2, hp⟩, hi, rfl, ?_, ?_⟩
    · change t = 2 * i.val + t % 2
      omega
    · change t % 2 < 2
      omega
  · left
    have hr : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hr with hr | hr
    · have hzero : (C.gates[i.val]).args.length = 0 := by omega
      have ht₀ : t = 2 * i.val := by omega
      simpa only [ht₀] using SelectedFields.stage_first_of_arity_zero C v i hzero
    · have hsmall : (C.gates[i.val]).args.length ≤ 1 := by omega
      have ht₁ : t = 2 * i.val + 1 := by omega
      simpa only [ht₁, Nat.add_assoc] using
        SelectedFields.stage_second_of_arity_le_one C v hA hconsistency i hsmall

/-- Every step below twice the gate count either has unchanged labels or is
the substep of an actual argument at position zero or one. This is the shorter
consumer interface to `step_cases_exact`. [PS10, Theorem 163.7] -/
theorem step_cases (t : ℕ) (ht : t < 2 * C.gates.length) :
    GateHybrids.stageBit C v t = GateHybrids.stageBit C v (t + 1) ∨
      ∃ i : Fin C.gates.length, ∃ p : Fin (C.gates[i.val]).args.length,
        t = 2 * i.val + p.val ∧ p.val < 2 :=
  (step_cases_exact C v hA hconsistency t ht).imp (fun h => h)
    (fun ⟨i, p, _, _, hclock, hpos⟩ => ⟨i, p, hclock, hpos⟩)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateStepCases
