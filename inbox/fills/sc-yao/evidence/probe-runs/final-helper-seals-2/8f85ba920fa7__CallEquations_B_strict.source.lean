/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.OTInputs
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
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
# The bit-OT input machines and a product call index

The input machines use a flat unary call index, while a circuit protocol labels a call
by an input-wire index and a key-bit index. The public finite-product equivalence relates
these forms. The contracts below take the circuit protocol's input-bit equations as
hypotheses, without referring to any concrete protocol or seed definition.

## Main definitions

None.

## Main results

* `CallEquations.inputA_eq`: the two sender bits agree with the flat coin-reading machine.
* `CallEquations.inputB_eq`: the receiver bit agrees with the unary-quotient machine.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (one ideal bit transfer per bit of each input-wire key).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.CallEquations

open Complexity Turing

/-- If call `(i,t)` reads its two bits at `(b S(n) + A(n) + i) n + t`,
then `otInputA A S ⟨1^n, ⟨x, ⟨r, 1^j⟩⟩⟩ = List.ofFn (call j)`.
This includes `n = 0`, when there is no call index. [PS10, Protocol 162.6] -/
theorem inputA_eq (A S : PolyExpr) (n m : ℕ) (x r : List Bool)
    (call : Fin (m * n) → Fin 2 → Bool)
    (hcall : ∀ (i : Fin m) (t : Fin n) (c : Fin 2),
      call (finProdFinEquiv (i, t)) c =
        r.getD (((decide ((c : ℕ) = 1)).toNat * S.eval n + A.eval n + i) * n + t) false)
    (j : Fin (m * n)) :
    OTInputs.otInputA A S (pairEncode (List.replicate n true)
      (pairEncode x (pairEncode r (List.replicate j true)))) = List.ofFn (call j) := by
  obtain ⟨⟨i, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := m) (n := n)).surjective j
  rw [OTInputs.otInputA_layout]
  norm_num only [List.ofFn_succ, List.ofFn_zero, hcall, finProdFinEquiv_apply_val,
    Fin.val_zero, Fin.val_succ, decide_false, decide_true, Bool.toNat_false, Bool.toNat_true]
  congr 2 <;> ring

/-- If call `(i,t)` chooses `x[i]`, then the receiver's unary-quotient machine returns
that call's singleton bit: `otInputB ⟨1^n, ⟨x, ⟨r, 1^j⟩⟩⟩ = List.ofFn (call j)`.
This includes `n = 0`, when there is no call index. [PS10, Protocol 162.6] -/
theorem inputB_eq (n m : ℕ) (x r : List Bool)
    (call : Fin (m * n) → Fin 1 → Bool)
    (hcall : ∀ (i : Fin m) (t : Fin n) (c : Fin 1),
      call (finProdFinEquiv (i, t)) c = x.getD i false)
    (j : Fin (m * n)) :
    OTInputs.otInputB (pairEncode (List.replicate n true)
      (pairEncode x (pairEncode r (List.replicate j true)))) = List.ofFn (call j) := by
  obtain ⟨⟨i, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := m) (n := n)).surjective j
  rw [OTInputs.otInputB_layout, finProdFinEquiv_apply_val]
  have ht := t.isLt
  have hdiv : ((t : ℕ) + n * i) / n = i := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
  rw [hdiv]
  simp only [List.ofFn_succ, List.ofFn_zero, hcall]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CallEquations
