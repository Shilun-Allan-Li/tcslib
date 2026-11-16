/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRead
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
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
# Polynomial-time garbling coin addresses

These contracts are generic in polynomial-time numeric and word maps. A consumer supplies
its own key, nonce, and shift equations. No seed or circuit-family definition is duplicated.

## Main definitions

None.

## Main results

* `CoinGarbling.keyWord_poly`: an addressed key block is polynomial-time.
* `CoinGarbling.assignmentIndex_poly`: a two-bit assignment index is polynomial-time in unary.
* `CoinGarbling.rowCoinWord_poly`: either half of an addressed row nonce is polynomial-time.
* `CoinGarbling.shiftBit_poly`: a fixed position of a gate's XOR shift is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (keys and independent encryption coins).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling

open Complexity Turing TCSlib.Cryptography.EncodingMachines

/-- A supplied key with block equation
`key z t = (coins z).getD (((bit z).toNat · bound z + vertex z) · width z + t) false`
is polynomial-time as a word when its coin, unary-number, and bit maps are polynomial-time.
[PS10, Protocol 162.6], addressing one of the two keys at a vertex. -/
theorem keyWord_poly {coins : List Bool → List Bool} {width bound vertex : List Bool → ℕ}
    {bit : List Bool → Bool} {key : ∀ z, Fin (width z) → Bool}
    (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hvertex : PolyTimeComputable fun z => List.replicate (vertex z) true)
    (hbit : PolyTimeComputable fun z => [bit z])
    (hkey : ∀ z t, key z t =
      (coins z).getD (((bit z).toNat * bound z + vertex z) * width z + t) false) :
    PolyTimeComputable fun z => List.ofFn (key z) := by
  have hoff := unaryMul_poly
    (unaryAdd_poly (unaryMul_poly (unaryOfTest_poly hbit) hbound) hvertex) hwidth
  refine (polyTimeComputable_window hcoins hoff hwidth).congr fun z => ?_
  apply congrArg List.ofFn
  funext t
  exact (hkey z t).symm

/-- The unary two-bit assignment index `b₀ + 2 b₁` is polynomial-time when both bits are:
`z ↦ 1^((b₀ z).toNat + 2 · (b₁ z).toNat)`. [PS10, Protocol 162.6] -/
theorem assignmentIndex_poly {b₀ b₁ : List Bool → Bool}
    (h₀ : PolyTimeComputable fun z => [b₀ z])
    (h₁ : PolyTimeComputable fun z => [b₁ z]) :
    PolyTimeComputable fun z =>
      List.replicate ((b₀ z).toNat + 2 * (b₁ z).toNat) true :=
  unaryAdd_poly (unaryOfTest_poly h₀) (unaryMul_poly (unaryConst_poly 2) (unaryOfTest_poly h₁))

/-- A supplied row nonce with block equation
`nonce z t = (coins z).getD (2 · bound z · width z +
 (4 · gate z + index z) · (2 · width z) + half.toNat · width z + t) false`
is polynomial-time as a word when the coin and unary-number maps are polynomial-time.
The fixed bit `half` selects the first or second nonce. [PS10, Protocol 162.6] -/
theorem rowCoinWord_poly {coins : List Bool → List Bool}
    {width bound gate index : List Bool → ℕ} {nonce : ∀ z, Fin (width z) → Bool}
    (half : Bool) (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hindex : PolyTimeComputable fun z => List.replicate (index z) true)
    (hnonce : ∀ z t, nonce z t =
      (coins z).getD (2 * bound z * width z + (4 * gate z + index z) * (2 * width z) +
        half.toNat * width z + t) false) :
    PolyTimeComputable fun z => List.ofFn (nonce z) := by
  have hoff := unaryAdd_poly
    (unaryAdd_poly (unaryMul_poly (unaryMul_poly (unaryConst_poly 2) hbound) hwidth)
      (unaryMul_poly (unaryAdd_poly (unaryMul_poly (unaryConst_poly 4) hgate) hindex)
        (unaryMul_poly (unaryConst_poly 2) hwidth)))
    (unaryMul_poly (unaryConst_poly half.toNat) hwidth)
  refine (polyTimeComputable_window hcoins hoff hwidth).congr fun z => ?_
  apply congrArg List.ofFn
  funext t
  exact (hnonce z t).symm

/-- Position `j` of a gate's shift is polynomial-time:
`z ↦ [(coins z).getD (10 · bound z · width z + 2 · gate z + j) false]`,
when the coin and unary-number maps are polynomial-time. [PS10, Protocol 162.6] -/
theorem shiftBit_poly {coins : List Bool → List Bool} {width bound gate : List Bool → ℕ}
    (j : ℕ) (hcoins : PolyTimeComputable coins)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true) :
    PolyTimeComputable fun z =>
      [(coins z).getD (10 * bound z * width z + 2 * gate z + j) false] := by
  exact getBit_poly hcoins
    (unaryAdd_poly
      (unaryAdd_poly (unaryMul_poly (unaryMul_poly (unaryConst_poly 10) hbound) hwidth)
        (unaryMul_poly (unaryConst_poly 2) hgate)) (unaryConst_poly j))

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinGarbling
