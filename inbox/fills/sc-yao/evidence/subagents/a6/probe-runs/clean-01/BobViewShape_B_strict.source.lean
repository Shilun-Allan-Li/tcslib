/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TwoMoveViews
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer
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
# The exact Bob-view shape of an OT-hybrid two-message protocol

A deterministic Bob receives only Alice's first main-phase message. His complete private
input contains his original input and the ideal OT answers. This interface extracts that
encoded view from the existing two-message view contract, with arbitrary raw input words.

## Main definitions

None.

## Main results

* `BobViewShape.encode_viewV_eq`: the actual encoded view has the canonical hybrid shape.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 and Theorem 163.7 (Bob's OT-hybrid view).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobViewShape

open Complexity Turing TCSlib.Cryptography

/-- In an Alice-first two-message OT-hybrid protocol with a zero-coin Bob, if Alice's
empty-history message is `first |w| (fst zA) rA`, then Bob's actual encoded view is
`View.encode ⟨1^n, ⟨ys, H.answersB ...⟩, [], [first n xs rA]⟩`. The inputs `xs` and `ys`
are arbitrary raw words, and no hypothesis on Bob's reply is required.
[PS10, Protocol 162.6 and Theorem 163.7]

**Proof sketch.** The public coin-length equation turns Bob's constant-zero coin polynomial
into a zero-length tape, whose list encoding is empty. Normalize the unary parameter length
only inside the nondependent message function, by congruence, so no typed execution tape
is transported. Instantiate the existing two-message encoded-view contract with Alice's
supplied sender equation and Bob's actual next function on a singleton history. The latter
satisfies its reply equation reflexively. Finally read the hybrid private-input equations:
Alice's first projection is `xs`, and Bob's private input pairs `ys` with his ideal answers. -/
theorem encode_viewV_eq (H : HybridProtocol otFunctionality)
    (first : ℕ → List Bool → List Bool → List Bool)
    (hRounds : H.main.rounds = .const 2) (hFirst : H.main.verifierFirst = false)
    (hBobCoins : H.main.V.coins = .const 0)
    (hSender : ∀ w z r, H.main.P.next w z r [] = first w.length (pairFstD z) r)
    (n : ℕ) (xs ys : List Bool) (r : H.Coins n) :
    (H.main.viewV (List.replicate n true)
      (H.privA n xs ys (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n xs ys (List.ofFn r.1) (List.ofFn r.2)) r).encode =
      (⟨List.replicate n true,
        pairEncode ys (H.answersB n xs ys (List.ofFn r.1) (List.ofFn r.2)), [],
        [first n xs (List.ofFn r.1)]⟩ : View).encode := by
  have hBob : List.ofFn r.2 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_ofFn]
    rw [Strategy.coinLen_eq, hBobCoins, PolyExpr.eval_const]
  have hMsg : first (List.replicate n true).length xs (List.ofFn r.1) =
      first n xs (List.ofFn r.1) :=
    congrArg (fun k => first k xs (List.ofFn r.1))
      (List.length_replicate (n := n) (a := true))
  rw [TwoMoveViews.encode_viewV_eq H.main
    (fun w z r => first w.length (pairFstD z) r)
    (fun w z r a => H.main.V.next w z r [a]) hRounds hFirst hSender
    (fun _ _ _ _ => rfl)]
  simp only [HybridProtocol.pairFstD_privA, hMsg, hBob, HybridProtocol.privB_eq,
    View.encode_mk]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobViewShape
