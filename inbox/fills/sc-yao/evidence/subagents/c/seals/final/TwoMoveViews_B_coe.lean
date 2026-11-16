/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid
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
# Views of an Alice-first two-message protocol

These identities compute transcripts, views, outputs and real samplers from the
next-message equations of arbitrary strategies. They apply to a two-message main
phase in the hybrid model, without any circuit or garbling definitions.

## Main definitions

This module introduces no definitions.

## Main results

* `transcriptWith_eq`: the parties receive `[msgB]` and `[msgA]`.
* `viewP_eq`, `viewV_eq`: their views have exactly these received-message components.
* `outV_eq`, `outP_eq`: Bob outputs his message; an echoing Alice outputs the same word.
* `realA_eq`, `realB_eq`: pointwise equations for the two hybrid real samplers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7.
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University
  Press, 2004, §7.3 (the oracle-aided hybrid model).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews

open Complexity Turing TCSlib.Cryptography

variable (π : Protocol)
  (msgA : List Bool → List Bool → List Bool → List Bool)
  (msgB : List Bool → List Bool → List Bool → List Bool → List Bool)
  (hR : π.rounds = .const 2) (hF : π.verifierFirst = false)
  (hA : ∀ w z r, π.P.next w z r [] = msgA w z r)
  (hB : ∀ w z r a, π.V.next w z r [a] = msgB w z r a)

include hR hF hA hB

/-- In an Alice-first two-message protocol, with first message `a = msgA w zA rA`
and reply `b = msgB w zB rB a`, the transcript is `([b], [a])`:
`π.transcriptWith π.P w zA zB r = ([b], [a])`. [PS10, Protocol 162.6] -/
theorem transcriptWith_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.transcriptWith π.P w zA zB r =
      ([msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))],
        [msgA w zA (List.ofFn r.1)]) := by
  simp [Protocol.transcriptWith_eq, hR, hF, PolyExpr.eval_const, exec_succ, exec_zero,
    moverIsV_false, hA, hB]

/-- The honest transcript of an Alice-first two-message protocol is `([b], [a])`,
where `a = msgA w zA rA` and `b = msgB w zB rB a`. [PS10, Protocol 162.6] -/
theorem transcript_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.transcript w zA zB r =
      ([msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))],
        [msgA w zA (List.ofFn r.1)]) := by
  rw [Protocol.transcript_eq_transcriptWith,
    transcriptWith_eq π msgA msgB hR hF hA hB]

/-- Alice's view in an Alice-first two-message protocol is
`⟨w, zA, rA, [msgB w zB rB (msgA w zA rA)]⟩`. [PS10, Theorem 163.7] -/
theorem viewP_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.viewP w zA zB r =
      ⟨w, zA, List.ofFn r.1,
        [msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))]⟩ := by
  rw [Protocol.viewP_eq, transcriptWith_eq π msgA msgB hR hF hA hB]

/-- Bob's view in an Alice-first two-message protocol is
`⟨w, zB, rB, [msgA w zA rA]⟩`. [PS10, Theorem 163.7] -/
theorem viewV_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.viewV w zA zB r = ⟨w, zB, List.ofFn r.2, [msgA w zA (List.ofFn r.1)]⟩ := by
  rw [Protocol.viewV_eq, transcriptWith_eq π msgA msgB hR hF hA hB]

/-- Alice's encoded view is
`⟨⟨w, zA⟩, ⟨rA, encodeMsgs [msgB w zB rB (msgA w zA rA)]⟩⟩`.
[PS10, Theorem 163.7] -/
theorem encode_viewP_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    (π.viewP w zA zB r).encode =
      pairEncode (pairEncode w zA) (pairEncode (List.ofFn r.1)
        (Strategy.encodeMsgs [msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1))])) := by
  rw [viewP_eq π msgA msgB hR hF hA hB, View.encode_mk]

/-- Bob's encoded view is `⟨⟨w, zB⟩, ⟨rB, encodeMsgs [msgA w zA rA]⟩⟩`.
[PS10, Theorem 163.7] -/
theorem encode_viewV_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    (π.viewV w zA zB r).encode =
      pairEncode (pairEncode w zB)
        (pairEncode (List.ofFn r.2) (Strategy.encodeMsgs [msgA w zA (List.ofFn r.1)])) := by
  rw [viewV_eq π msgA msgB hR hF hA hB, View.encode_mk]

/-- Bob's output is the reply he sent:
`π.outV π.P w zA zB r = msgB w zB rB (msgA w zA rA)`.
[PS10, Protocol 162.6, D8 verdict convention] -/
theorem outV_eq (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.outV π.P w zA zB r =
      msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1)) := by
  rw [Protocol.outV_eq, transcriptWith_eq π msgA msgB hR hF hA hB]
  exact hB _ _ _ _

/-- If Alice outputs the unique message she received, then her output is Bob's reply:
`π.outP w zA zB r = msgB w zB rB (msgA w zA rA)`.
[PS10, Protocol 162.6] -/
theorem outP_eq (hEcho : ∀ w z r b, π.P.next w z r [b] = b)
    (w zA zB : List Bool) (r : π.ExecCoins π.P w) :
    π.outP w zA zB r = msgB w zB (List.ofFn r.2) (msgA w zA (List.ofFn r.1)) := by
  rw [Protocol.outP_eq, transcriptWith_eq π msgA msgB hR hF hA hB]
  exact hEcho _ _ _ _

omit hR hF hA hB

variable {G : Functionality} (H : HybridProtocol G)
  (hRounds : H.main.rounds = .const 2) (hFirst : H.main.verifierFirst = false)
  (hSender : ∀ w z r, H.main.P.next w z r [] = msgA w z r)
  (hReply : ∀ w z r a, H.main.V.next w z r [a] = msgB w z r a)

include hRounds hFirst hSender hReply

/-- For an Alice-first two-message hybrid main phase, Alice's real sampler is
`⟨⟨⟨1^n, zA⟩, ⟨rA, encodeMsgs [b]⟩⟩, b⟩`, where `zA`, `zB` are the complete
hybrid private inputs, `a = msgA (1^n) zA rA`, and `b = msgB (1^n) zB rB a`.
The identity is pointwise in the joint coin sample `r`. [PS10, Theorem 163.7] -/
theorem realA_eq (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n) :
    H.realA F n x y r =
      let w := List.replicate n true
      let zA := H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)
      let zB := H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)
      let a := msgA w zA (List.ofFn r.1)
      let b := msgB w zB (List.ofFn r.2) a
      pairEncode (pairEncode (pairEncode w zA)
        (pairEncode (List.ofFn r.1) (Strategy.encodeMsgs [b]))) b := by
  rw [HybridProtocol.realA_eq,
    encode_viewP_eq H.main msgA msgB hRounds hFirst hSender hReply,
    outV_eq H.main msgA msgB hRounds hFirst hSender hReply]

/-- If Alice echoes her received message, Bob's real sampler in an Alice-first
two-message hybrid main phase is `⟨⟨⟨1^n, zB⟩, ⟨rB, encodeMsgs [a]⟩⟩, b⟩`,
where `zA`, `zB` are the complete private inputs, `a = msgA (1^n) zA rA`, and
`b = msgB (1^n) zB rB a`. This is pointwise in `r`. [PS10, Theorem 163.7] -/
theorem realB_eq (hEcho : ∀ w z r b, H.main.P.next w z r [b] = b)
    (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n) :
    H.realB F n x y r =
      let w := List.replicate n true
      let zA := H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)
      let zB := H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)
      let a := msgA w zA (List.ofFn r.1)
      let b := msgB w zB (List.ofFn r.2) a
      pairEncode (pairEncode (pairEncode w zB)
        (pairEncode (List.ofFn r.2) (Strategy.encodeMsgs [a]))) b := by
  rw [HybridProtocol.realB_eq,
    encode_viewV_eq H.main msgA msgB hRounds hFirst hSender hReply,
    outP_eq H.main msgA msgB hRounds hFirst hSender hReply hEcho]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.TwoMoveViews
