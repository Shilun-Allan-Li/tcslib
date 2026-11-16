/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TwoMoveViews
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
# Message bounds for an Alice-first two-move protocol

The generic transcript equation reduces its message-size bound to the first-message and
reply bounds, on arbitrary private inputs and tapes. The garbling envelope records the
explicit polynomial supplied by the generic table, input-key and decoding-pair bounds.

## Main definitions

* `aliceMessageBound`: the polynomial envelope for a garbling message.

## Main results

* `aliceMessageBound_eq`: the envelope is `2 S (112 n + 82) + 2 A (2 n + 2) + O (6 n + 6) + 4`.
* `twoMove_message_length_le`: two move bounds imply a bound on every transcript message.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Definition 155.1 and Protocol 162.6 (efficiency and message lengths).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing TCSlib.Cryptography

/-- The garbling-message envelope at `n` is
`2 S(n) (112 n + 82) + 2 A(n) (2 n + 2) + O(n) (6 n + 6) + 4`.
[PS10, Protocol 162.6] -/
def aliceMessageBound (S A O : PolyExpr) : PolyExpr :=
  .add (.add (.add
    (.mul (.const 2) (.mul S (.add (.mul (.const 112) .var) (.const 82))))
    (.mul (.const 2) (.mul A (.add (.mul (.const 2) .var) (.const 2)))))
    (.mul O (.add (.mul (.const 6) .var) (.const 6)))) (.const 4)

/-- Evaluating the garbling-message envelope gives its explicit bound:
`(aliceMessageBound S A O).eval n = 2 S(n) (112 n + 82) + 2 A(n) (2 n + 2) + O(n) (6 n + 6) + 4`.
[PS10, Protocol 162.6] -/
theorem aliceMessageBound_eq (S A O : PolyExpr) (n : ℕ) :
    (aliceMessageBound S A O).eval n =
      2 * (S.eval n * (112 * n + 82)) + 2 * (A.eval n * (2 * n + 2)) +
        O.eval n * (6 * n + 6) + 4 := by
  simp only [aliceMessageBound, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_const, PolyExpr.eval_var]

/-- In an Alice-first protocol with two messages, bounds `BA(|w|)` and `BB(|w|)` on
the first message and reply imply bound `(BA + BB)(|w|)` on every transcript message,
for arbitrary private inputs and tapes. [PS10, Definition 155.1; Protocol 162.6] -/
theorem twoMove_message_length_le (π : Protocol)
    (msgA : List Bool → List Bool → List Bool → List Bool)
    (msgB : List Bool → List Bool → List Bool → List Bool → List Bool)
    (hR : π.rounds = .const 2) (hF : π.verifierFirst = false)
    (hA : ∀ w z r, π.P.next w z r [] = msgA w z r)
    (hB : ∀ w z r a, π.V.next w z r [a] = msgB w z r a)
    (BA BB : PolyExpr)
    (hLA : ∀ w z r, (msgA w z r).length ≤ BA.eval w.length)
    (hLB : ∀ w z r a, (msgB w z r a).length ≤ BB.eval w.length)
    (w zA zB : List Bool) (r : π.ExecCoins π.P w) (msg : List Bool)
    (hmsg : msg ∈ (π.transcript w zA zB r).1 ++ (π.transcript w zA zB r).2) :
    msg.length ≤ (PolyExpr.add BA BB).eval w.length := by
  rw [TwoMoveViews.transcript_eq π msgA msgB hR hF hA hB w zA zB r] at hmsg
  simp only [List.mem_append, List.mem_singleton] at hmsg
  rcases hmsg with rfl | rfl
  · exact (hLB _ _ _ _).trans (by rw [PolyExpr.eval_add]; omega)
  · exact (hLA _ _ _).trans (by rw [PolyExpr.eval_add]; omega)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
