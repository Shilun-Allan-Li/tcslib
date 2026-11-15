/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Data.Fin.Tuple.Basic
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
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
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
# Marginals of the keys and coins of nested encryption

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.GarblingCoins.pushesUniform_position_keys_coin`: two distinct key
  choices at one position and either nonce are an independent uniform triple.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Claim 157.a (ii).
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingCoins

open TCSlib.Cryptography

/-- Two distinct choices at one position and either coin form a uniform triple:
`(ks,(r₀,r₁)) ↦ (ks j b,ks j b',if c then r₁ else r₀)` pushes uniform to uniform,
for `b ≠ b'`. -/
theorem pushesUniform_position_keys_coin {K : Type} [Fintype K] [Nonempty K]
    {len : ℕ} (j : Fin len) {b b' : Bool} (hb : b ≠ b') (c : Bool) :
    HardcoreBit.PushesUniform (fun t : (Fin len → Bool → K) × (K × K) =>
      (t.1 j b, t.1 j b', if c then t.2.2 else t.2.1)) := by
  have hk := (HardcoreBit.pushesUniform_eval j).comp
    (HardcoreBit.pushesUniform_eval_pair (γ := K) hb)
  cases c
  · exact (hk.prodMap HardcoreBit.pushesUniform_fst).comp
      (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))
  · exact (hk.prodMap HardcoreBit.pushesUniform_snd).comp
      (HardcoreBit.pushesUniform_equiv (Equiv.prodAssoc K K K))

/-- A failure probability greater than `1-ε` bounds success strictly by `ε`:
`1-ε < Pr[X = none] → Pr[X.isSome = true] < ε`. -/
theorem uprob_isSome_lt_of_none {Ω α : Type} [Fintype Ω] [Nonempty Ω]
    (X : Ω → Option α) {ε : ℝ} (h : 1 - ε < uprob (fun t => X t = none)) :
    uprob (fun t => (X t).isSome = true) < ε := by
  rw [OneWay.uprob_congr (fun t : Ω => Option.isSome_iff_ne_none), uprob_not]
  linarith

end TCSlib.Cryptography.SecureComputation.GarblingCoins
