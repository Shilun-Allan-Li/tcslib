/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
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
            (true && coe && projection)
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
# Statistical switches outside a bad event

Two samplers driven by the same finite coin space have statistical distance at most
the probability of an event outside which they agree. These contracts specialize the
published expectation coupling bound to event indicators, for the statistical parts
of [PS10, Theorem 163.7]. They include empty finite coin spaces.

## Main definitions

This module introduces no definitions.

## Main results

* `statClose_of_eq_off`: agreement outside `Bad` gives closeness at most `Pr[Bad]`.
* `distAdv_le_of_eq_off`: every randomized distinguisher inherits the same bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (the statistical output switch).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch

open TCSlib.Cryptography

/-- For samplers `X`, `Y` on the same finite coin space, event `Bad` and bound `δ`,
`Pr[Bad] ≤ δ` and `X r = Y r` outside `Bad` imply `StatClose X Y δ`.
[PS10, Theorem 163.7, statistical switch]

**Proof sketch.** For each test set, write both probabilities as expectations of
its zero-one indicators. The public expectation coupling bound applies because
the indicators lie in `[0,1]` and agree outside `Bad`; its bound is at most `δ`. -/
theorem statClose_of_eq_off {σ γ : Type*} [Fintype σ] (X Y : σ → γ)
    (Bad : σ → Prop) (δ : ℝ) (hBad : uprob Bad ≤ δ)
    (heq : ∀ r, ¬ Bad r → X r = Y r) : StatClose X Y δ := by
  classical
  rw [statClose_iff]
  intro T
  rw [uprob_eq_uexp, uprob_eq_uexp]
  refine (MultiMsg.abs_uexp_sub_le_uprob
    (fun r => if T (X r) then (1 : ℝ) else 0)
    (fun r => if T (Y r) then (1 : ℝ) else 0) Bad ?_ ?_ ?_).trans hBad
  · intro r
    dsimp only
    split_ifs <;> norm_num
  · intro r
    dsimp only
    split_ifs <;> norm_num
  · intro r hr
    simp only [heq r hr]

/-- For same-coins samplers `X`, `Y` agreeing outside an event of probability at most
`δ`, every randomized distinguisher `D` has `distAdv X Y D ≤ δ`.
[PS10, Theorem 163.7, statistical switch] -/
theorem distAdv_le_of_eq_off {σ γ ρ : Type*} [Fintype σ] [Fintype ρ]
    (X Y : σ → γ) (Bad : σ → Prop) (δ : ℝ) (hBad : uprob Bad ≤ δ)
    (heq : ∀ r, ¬ Bad r → X r = Y r) (D : γ → ρ → Bool) :
    distAdv X Y D ≤ δ :=
  distAdv_le_of_statClose X Y (statClose_of_eq_off X Y Bad δ hBad heq) D

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch
