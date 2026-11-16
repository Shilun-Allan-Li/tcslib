/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinSeedRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
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
# Exact sampler transport at the gate-hybrid endpoints

The real sampler and its encoded-view equation are parameters. Its seed has
the four addressed tape readers. The proved tape relabeling and per-seed view
identity therefore identify its acceptance probability with stage zero.
The last stage is the existing canonical fake view, with prescribed result
bits. This module defines no protocol, real message, or probability measure.

## Main definitions

None.

## Main results

* `real_eq_stage0_on_tape`: the pointwise complete-tape relabeling identity.
* `acceptProb_real_eq_stage0`: exact acceptance equality for every distinguisher.
* `acceptProb_real_eq_stage0_fst`: the same equality with an ignored Bob tape.
* `sample_end_of_result`: the exact prescribed-result canonical fake endpoint.
* `acceptProb_end_eq_ideal`: exact final acceptance transport through any coin bijection.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the Bob-view hybrid).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes,
  UC Berkeley, draft of 22 January 2026, §3.2, Lemmas 3.2 and 3.3.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints

open Complexity Turing BoolCircuit TCSlib.Cryptography

section Tape

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
  (commonInput bobInput bobCoins aliceOutput : List Bool)
  (real : (Fin (10 * S * n + 2 * S) → Bool) → List Bool)
  (hReal : ∀ r, real r =
    pairEncode (⟨commonInput,
      pairEncode bobInput (List.ofFn fun t : Fin (inB * n) =>
        keyAt C (seed (List.ofFn r)) (inA + t.divNat) (v (inA + t.divNat)) t.modNat),
      bobCoins,
      [pairEncode (BinArith.encWords (List.ofFn fun i =>
          BinArith.encWords (garbledTable M C (seed (List.ofFn r)) i)))
        (pairEncode
          (BinArith.encWords (List.ofFn fun w : Fin inA =>
            List.ofFn (keyAt C (seed (List.ofFn r)) w (v w))))
          (BinArith.encWords (List.ofFn fun j =>
            pairEncode (List.ofFn (keyAt C (seed (List.ofFn r)) (output j) false))
              (List.ofFn (keyAt C (seed (List.ofFn r)) (output j) true)))))]⟩ : View).encode
      aliceOutput)

include hA hS hK hR₀ hR₁ hP hReal

/-- The supplied real sampler equals stage zero on the explicitly relabeled
complete tape, using its four seed readers and encoded-view equation.
The tape has length `10*S*n+2*S`, including when `n=0`. [PS10, Theorem 163.7] -/
theorem real_eq_stage0_on_tape (r : Fin (10 * S * n + 2 * S) → Bool) :
    real r = GateHybridMessage.sample M C
      (seed (List.ofFn (CoinRelabel.relabel S n (CoinSeedRelabel.keyMask C S v)
        (CoinSeedRelabel.rowPerm C S hA v) (CoinSeedRelabel.shiftMask C S v) r)))
      inA inB outLen output v commonInput bobInput bobCoins aliceOutput 0 := by
  rw [hReal]
  rw [CoinSeedRelabel.seed_relabel C S n hA v hS seed hK hR₀ hR₁ hP r]
  exact GateHybridMessage.sample_relabel M C (seed (List.ofFn r)) inA inB outLen
    output v commonInput bobInput bobCoins aliceOutput

/-- Every randomized distinguisher has exactly the same acceptance probability
on the supplied real sampler and the uniform stage-zero sampler. This is the
published uniform change-of-coins lemma specialized to the proved tape bijection.
[PS10, Theorem 163.7; Gar26, §3.2]

**Proof sketch.** The pointwise reader identifies the real sampler with stage
zero precomposed by the complete-tape permutation. Apply the existing uniform
reseeding equation to that permutation and the supplied distinguisher. -/
theorem acceptProb_real_eq_stage0 {κ : Type*} [Fintype κ]
    (D : List Bool → κ → Bool) :
    acceptProb real D = acceptProb
      (fun r : Fin (10 * S * n + 2 * S) → Bool =>
        GateHybridMessage.sample M C (seed (List.ofFn r)) inA inB outLen output v
          commonInput bobInput bobCoins aliceOutput 0) D := by
  have h : real = fun r => GateHybridMessage.sample M C
      (seed (List.ofFn (CoinRelabel.relabel S n (CoinSeedRelabel.keyMask C S v)
        (CoinSeedRelabel.rowPerm C S hA v) (CoinSeedRelabel.shiftMask C S v) r)))
      inA inB outLen output v commonInput bobInput bobCoins aliceOutput 0 := by
    funext r
    exact real_eq_stage0_on_tape C S n hA v hS seed hK hR₀ hR₁ hP M
      inA inB outLen output commonInput bobInput bobCoins aliceOutput real hReal r
  rw [h]
  exact acceptProb_comp_equiv
    (CoinRelabel.relabel S n (CoinSeedRelabel.keyMask C S v)
      (CoinSeedRelabel.rowPerm C S hA v) (CoinSeedRelabel.shiftMask C S v))
    (fun r => GateHybridMessage.sample M C (seed (List.ofFn r)) inA inB outLen output v
      commonInput bobInput bobCoins aliceOutput 0) D

/-- An independent Bob tape ignored by the real sampler can be dropped before
the same stage-zero acceptance equality. This directly reuses `acceptProb_fst`.
[PS10, Theorem 163.7; Gar26, §3.2] -/
theorem acceptProb_real_eq_stage0_fst {τ κ : Type*} [Fintype τ] [Nonempty τ]
    [Fintype κ] (D : List Bool → κ → Bool) :
    acceptProb (fun r : (Fin (10 * S * n + 2 * S) → Bool) × τ => real r.1) D =
      acceptProb (fun r : Fin (10 * S * n + 2 * S) → Bool =>
        GateHybridMessage.sample M C (seed (List.ofFn r)) inA inB outLen output v
          commonInput bobInput bobCoins aliceOutput 0) D := by
  rw [acceptProb_fst]
  exact acceptProb_real_eq_stage0 C S n hA v hS seed hK hR₀ hR₁ hP M
    inA inB outLen output commonInput bobInput bobCoins aliceOutput real hReal D

/-- The supplied real and stage-zero samplers have zero distinguishing
advantage for every randomized distinguisher. [PS10, Theorem 163.7] -/
theorem distAdv_real_stage0_zero {κ : Type*} [Fintype κ]
    (D : List Bool → κ → Bool) :
    distAdv real (fun r : Fin (10 * S * n + 2 * S) → Bool =>
      GateHybridMessage.sample M C (seed (List.ofFn r)) inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput 0) D = 0 := by
  rw [distAdv_def, acceptProb_real_eq_stage0 C S n hA v hS seed hK hR₀ hR₁ hP M
    inA inB outLen output commonInput bobInput bobCoins aliceOutput real hReal D,
    sub_self, abs_zero]

end Tape

variable {inputs width : ℕ} {ρ : Type}

/-- When the output-wire values are the prescribed result bits, the last-stage
sample is the canonical fake view paired with the prescribed Alice output.
This is a pointwise identity and does not assume any simulator or coin type.
[PS10, Theorem 163.7] -/
theorem sample_end_of_result (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (result : Fin outLen → Bool) (hResult : ∀ j, v (output j) = result j)
    (commonInput bobInput bobCoins aliceOutput : List Bool) :
    GateHybridMessage.sample M C s inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput (2 * C.gates.length) =
      pairEncode (⟨commonInput,
        pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB)),
        bobCoins, [FakeObjects.message M C s inA outLen output result]⟩ : View).encode
        aliceOutput := by
  rw [GateHybridMessage.sample_end, funext hResult]

/-- The final-stage sampler has exactly the acceptance probability of the
canonical fake view over the same seed family. [PS10, Theorem 163.7]

**Proof sketch.** Apply the pointwise final-stage equation at every seed, then
transport the resulting function equality through the existing acceptance
functional. No summation or probability identity is re-derived. -/
theorem acceptProb_end_eq_fake {σ κ : Type*} [Fintype σ] [Fintype κ]
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (seed : σ → GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (result : Fin outLen → Bool) (hResult : ∀ j, v (output j) = result j)
    (commonInput bobInput bobCoins aliceOutput : List Bool) (D : List Bool → κ → Bool) :
    acceptProb (fun r => GateHybridMessage.sample M C (seed r) inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput (2 * C.gates.length)) D =
      acceptProb (fun r => pairEncode (⟨commonInput,
        pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C (seed r) inA inB)),
        bobCoins, [FakeObjects.message M C (seed r) inA outLen output result]⟩ : View).encode
        aliceOutput) D := by
  apply congrArg (fun X : σ → List Bool => acceptProb X D)
  funext r
  exact sample_end_of_result M C (seed r) inA inB outLen output v result hResult
    commonInput bobInput bobCoins aliceOutput

section Ideal

variable {σ τ : Type*} [Fintype σ] [Fintype τ]
  (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
  (seed : σ → GarbleSeed C (Fin width → Bool) ρ)
  (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
  (result : Fin outLen → Bool) (hResult : ∀ j, v (output j) = result j)
  (commonInput bobInput bobCoins aliceOutput : List Bool) (e : σ ≃ τ)
  (ideal : τ → List Bool)
  (hIdeal : ∀ r, ideal (e r) = pairEncode (⟨commonInput,
    pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C (seed r) inA inB)),
    bobCoins, [FakeObjects.message M C (seed r) inA outLen output result]⟩ : View).encode
    aliceOutput)

include hResult hIdeal

/-- A canonical fake-view equation for an ideal sampler, read through any coin
bijection `e`, identifies its acceptance probability with the last hybrid stage.
Only the published pointwise endpoint and uniform reseeding lemma are used.
[PS10, Theorem 163.7; Gar26, §3.2] -/
theorem acceptProb_end_eq_ideal {κ : Type*} [Fintype κ] (D : List Bool → κ → Bool) :
    acceptProb (fun r => GateHybridMessage.sample M C (seed r) inA inB outLen output v
      commonInput bobInput bobCoins aliceOutput (2 * C.gates.length)) D =
      acceptProb ideal D := by
  calc
    _ = acceptProb (fun r => ideal (e r)) D := by
      apply congrArg (fun X : σ → List Bool => acceptProb X D)
      funext r
      exact (sample_end_of_result M C (seed r) inA inB outLen output v result hResult
        commonInput bobInput bobCoins aliceOutput).trans (hIdeal r).symm
    _ = acceptProb ideal D := acceptProb_comp_equiv e ideal D

/-- The last hybrid stage and the supplied canonical ideal sampler have zero
distinguishing advantage for every randomized distinguisher.
This follows directly from their exact acceptance equality. [PS10, Theorem 163.7] -/
theorem distAdv_end_ideal_zero {κ : Type*} [Fintype κ] (D : List Bool → κ → Bool) :
    distAdv (fun r => GateHybridMessage.sample M C (seed r) inA inB outLen output v
      commonInput bobInput bobCoins aliceOutput (2 * C.gates.length)) ideal D = 0 := by
  rw [distAdv_def, acceptProb_end_eq_ideal M C seed inA inB outLen output v result
    hResult commonInput bobInput bobCoins aliceOutput e ideal hIdeal D, sub_self, abs_zero]

end Ideal

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints
