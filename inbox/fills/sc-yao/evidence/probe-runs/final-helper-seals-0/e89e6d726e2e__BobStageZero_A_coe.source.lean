/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SamplerEndpoints
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobViewShape
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.OTAnswerWords
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SimulationBound
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
# The actual receiver view at the first garbling hybrid

This consumer combines the established view shape, bit-transfer answer words, tape
normalization and complete-tape relabeling. The caller supplies only protocol and seed
readers and the first-message payload equation. No protocol or message is defined here.

## Main definitions

None.

## Main results

* `acceptProb_eq_stage0`: the actual view paired with any prescribed sender output has
  exactly the acceptance probability of the first garbling hybrid.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 and Theorem 163.7 (receiver-view coin relabeling).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStageZero

open Complexity Turing BoolCircuit TCSlib.Cryptography

variable {inputs : ℕ} (C : DAGCircuit inputs) (S n : ℕ)
  (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
  (hS : C.size ≤ S)
  (seed : List Bool → GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (hK : ∀ q (w : Fin C.size) b (t : Fin n),
    (seed q).1 w b t = q.getD ((b.toNat * S + w) * n + t) false)
  (hR₀ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).1 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
  (hR₁ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).2 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
  (hP : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
      (t : Fin (C.gates[i]).args.length),
    (seed q).2.2 i a t = xor (a t) (q.getD (10 * S * n + 2 * i + t) false))
  (M : MultiEnc (Fin n → Bool) (List Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (inA inB outLen : ℕ) (output : Fin outLen → ℕ)
  (H : HybridProtocol otFunctionality)
  (first : ℕ → List Bool → List Bool → List Bool)
  (hRounds : H.main.rounds = .const 2) (hFirst : H.main.verifierFirst = false)
  (hBobCoins : H.main.V.coins = .const 0)
  (hSender : ∀ w z r, H.main.P.next w z r [] = first w.length (pairFstD z) r)
  (xs ys aliceOutput : List Bool)
  (hLen : H.main.P.coinLen (List.replicate n true).length = 10 * S * n + 2 * S)
  (hCalls : H.calls.eval n = inB * n)
  (hvB : ∀ i : Fin inB, v (inA + i) = ys.getD i false)
  (hpoint : ∀ rA rB (i : Fin inB) (t : Fin n),
    (H.answersB n xs ys rA rB).getD (i * n + t) false =
      keyAt C (seed rA) (inA + i) (ys.getD i false) t)
  (hMessage : ∀ r, first n xs r =
    pairEncode (BinArith.encWords (List.ofFn fun i =>
      BinArith.encWords (garbledTable M C (seed r) i)))
      (pairEncode
        (BinArith.encWords (List.ofFn fun w : Fin inA =>
          List.ofFn (keyAt C (seed r) w (v w))))
        (BinArith.encWords (List.ofFn fun j =>
          pairEncode (List.ofFn (keyAt C (seed r) (output j) false))
            (List.ofFn (keyAt C (seed r) (output j) true))))))

include hA hS hK hR₀ hR₁ hP hRounds hFirst hBobCoins hSender hLen hCalls hvB hpoint hMessage

/-- If an Alice-first two-move bit-transfer hybrid has a zero-coin receiver, the supplied
payload and addressed seed readers, then its actual encoded receiver view paired with
`aliceOutput` has exactly the acceptance probability of stage zero over `10*S*n+2*S` bits.
The receiver's selected wire values agree with `ys`, and no positivity premise is needed.
[PS10, Protocol 162.6 and Theorem 163.7]

**Proof sketch.** Form a word sampler over the full normalized first tape, using the
supplied first-message function and the answers selected by the wire values. The answer
reader and bit-transfer call count identify the actual answer word with the active keys
under the relabeled seed. Read that seed through the existing active-answer relabeling
formula. The two-message view contract then gives the actual receiver view, including its
empty receiver tape. Normalize the first tape using the supplied length equality; its
word is preserved, so the existing first-tape probability contract drops the unused second
tape. Finally replace the first message by its supplied payload equation and invoke the
established complete-tape relabeling endpoint. Thus both probability changes use existing
uniform transport lemmas rather than any new summation or re-randomization argument. -/
theorem acceptProb_eq_stage0 {κ : Type*} [Fintype κ]
    (D : List Bool → κ → Bool) :
    acceptProb (fun r : H.Coins n => pairEncode
      (H.main.viewV (List.replicate n true)
        (H.privA n xs ys (List.ofFn r.1) (List.ofFn r.2))
        (H.privB n xs ys (List.ofFn r.1) (List.ofFn r.2)) r).encode aliceOutput) D =
    acceptProb (fun r : Fin (10 * S * n + 2 * S) → Bool =>
      GateHybridMessage.sample M C (seed (List.ofFn r)) inA inB outLen output v
        (List.replicate n true) ys [] aliceOutput 0) D := by
  let real := fun r : Fin (10 * S * n + 2 * S) → Bool =>
    pairEncode (⟨List.replicate n true,
      pairEncode ys (List.ofFn fun t : Fin (inB * n) =>
        keyAt C (seed (List.ofFn r)) (inA + t.divNat) (v (inA + t.divNat)) t.modNat), [],
      [first n xs (List.ofFn r)]⟩ : View).encode aliceOutput
  have hView (r : H.Coins n) :
      (H.main.viewV (List.replicate n true)
        (H.privA n xs ys (List.ofFn r.1) (List.ofFn r.2))
        (H.privB n xs ys (List.ofFn r.1) (List.ofFn r.2)) r).encode =
      (⟨List.replicate n true,
        pairEncode ys (List.ofFn fun t : Fin (inB * n) =>
          keyAt C (seed (List.ofFn r.1)) (inA + t.divNat) (v (inA + t.divNat)) t.modNat), [],
        [first n xs (List.ofFn r.1)]⟩ : View).encode := by
    have hAns := OTAnswerWords.answersB_eq_active H n xs ys
      (List.ofFn r.1) (List.ofFn r.2) C (seed (List.ofFn r.1)) inA inB v hCalls hvB
      (hpoint (List.ofFn r.1) (List.ofFn r.2))
    rw [BobViewShape.encode_viewV_eq H first hRounds hFirst hBobCoins hSender,
      hAns, GateHybridMessage.activeAnswers_relabel]
  trans acceptProb real D
  · apply acceptProb_firstTape H n _ hLen _ real _ D
    intro r
    simp only [hView, real, strategyTapeEquiv_ofFn]
  · apply SamplerEndpoints.acceptProb_real_eq_stage0 C S n hA v hS seed hK hR₀ hR₁ hP M
      inA inB outLen output (List.replicate n true) ys [] aliceOutput real _ D
    intro r
    simp only [real, hMessage]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStageZero
