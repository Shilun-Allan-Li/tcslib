/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.ZeroPEval

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The circuit-evaluation loop runs in polynomial time

The second half of the evaluator of `TCSlib.Complexity.Randomized.ZeroPEval`, for the class half
of [AB09, §7.2.3, p.130]: the gate step on words is polynomial-time and grows a state by a
bounded amount, so the loop `gateRun` (one step per letter of the code) is polynomial-time; on
the codes of well-formed circuits it computes their values modulo `k`, and it decides whether a
word is such a code.

## Main definitions

* `Randomized.PIT.gateRun` — the evaluation loop on `⟨ctx, code⟩`.
* `Randomized.PIT.validW`, `Randomized.PIT.evalModW` — the validity test and the output value.

## Main results

* `Randomized.PIT.polyTimeComputable_gateRun`, `Randomized.PIT.polyTimeComputable_validW`,
  `Randomized.PIT.polyTimeComputable_evalModW`.
* `Randomized.PIT.gateRun_encodeGates`, `Randomized.PIT.exists_of_runOk` — the loop runs
  exactly the codes of node lists whose nodes read earlier nodes.
* `Randomized.PIT.validW_iff` — `validW x` iff `x` encodes a well-formed circuit.
* `Randomized.PIT.evalModW_spec` — the value is `C(a) mod k`.
* `Randomized.PIT.polyTimeComputable_tagBit`, `polyTimeComputable_arg1W`,
  `polyTimeComputable_midW`, `polyTimeComputable_isVarW`, `polyTimeComputable_isOneW`,
  `polyTimeComputable_isDone`, `polyTimeComputable_restW` — the gate-reading word functions are
  polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

namespace PIT

open Complexity Turing BinArith AlgCircuit
open Complexity.LogProg (bitsVal bitsVal_bits)

variable {n : ℕ}

/-! ### Polynomial time -/

/-- `|f| < |g|` as a one-bit test. -/
theorem polyTimeComputable_ltLen {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun D => [decide ((f D).length < (g D).length)]) := by
  convert polyTimeComputable_not (polyTimeComputable_lenLe.comp (hf.pairEncode hg)) using 1
  funext D
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.cons.injEq, and_true]
  by_cases h : (f D).length < (g D).length
  · simp [h]
  · simp [h]; omega

/-- `tagBit` is polynomial-time. -/
theorem polyTimeComputable_tagBit (i : ℕ) : PolyTimeComputable (fun w => [tagBit i w]) :=
  polyTimeComputable_headD.comp (polyTimeComputable_drop i)

/-- `bodyW` is polynomial-time. -/
private theorem polyTimeComputable_bodyW : PolyTimeComputable bodyW := polyTimeComputable_drop 4

/-- `arg1W` is polynomial-time. -/
theorem polyTimeComputable_arg1W : PolyTimeComputable arg1W :=
  polyTimeComputable_uHead.comp polyTimeComputable_bodyW

/-- `midW` is polynomial-time. -/
theorem polyTimeComputable_midW : PolyTimeComputable midW :=
  polyTimeComputable_uRest.comp polyTimeComputable_bodyW

/-- `arg2W` is polynomial-time. -/
private theorem polyTimeComputable_arg2W : PolyTimeComputable arg2W :=
  polyTimeComputable_uHead.comp polyTimeComputable_midW

/-- `rest2W` is polynomial-time. -/
private theorem polyTimeComputable_rest2W : PolyTimeComputable rest2W :=
  polyTimeComputable_uRest.comp polyTimeComputable_midW

/-- `isVarW` is polynomial-time. -/
theorem polyTimeComputable_isVarW : PolyTimeComputable (fun w => [isVarW w]) := by
  have t := polyTimeComputable_tagBit
  exact polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_not (t 1))
    (polyTimeComputable_not (t 2))) (polyTimeComputable_not (t 3))

/-- `isOneW` is polynomial-time. -/
theorem polyTimeComputable_isOneW : PolyTimeComputable (fun w => [isOneW w]) := by
  have t := polyTimeComputable_tagBit
  exact polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_not (t 1))
    (polyTimeComputable_not (t 2))) (t 3)

/-- `isAddW` is polynomial-time. -/
private theorem polyTimeComputable_isAddW : PolyTimeComputable (fun w => [isAddW w]) := by
  have t := polyTimeComputable_tagBit
  exact polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_not (t 1)) (t 2))
    (polyTimeComputable_not (t 3))

/-- `isSubW` is polynomial-time. -/
private theorem polyTimeComputable_isSubW : PolyTimeComputable (fun w => [isSubW w]) := by
  have t := polyTimeComputable_tagBit
  exact polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_not (t 1)) (t 2)) (t 3)

/-- `isMulW` is polynomial-time. -/
private theorem polyTimeComputable_isMulW : PolyTimeComputable (fun w => [isMulW w]) := by
  have t := polyTimeComputable_tagBit
  exact polyTimeComputable_and (polyTimeComputable_and (t 1) (polyTimeComputable_not (t 2)))
    (polyTimeComputable_not (t 3))

/-- `isDone` is polynomial-time. -/
theorem polyTimeComputable_isDone : PolyTimeComputable (fun w => [isDone w]) :=
  polyTimeComputable_or polyTimeComputable_isNil
    (polyTimeComputable_and (polyTimeComputable_isNil.comp (polyTimeComputable_drop 1))
      (polyTimeComputable_not polyTimeComputable_headD))

/-- `restW` is polynomial-time. -/
theorem polyTimeComputable_restW : PolyTimeComputable restW :=
  polyTimeComputable_ite polyTimeComputable_isVarW polyTimeComputable_midW
    (polyTimeComputable_ite polyTimeComputable_isOneW polyTimeComputable_bodyW
      polyTimeComputable_rest2W)

/-- `sW` is polynomial-time. -/
private theorem polyTimeComputable_sW : PolyTimeComputable sW := polyTimeComputable_slot2

/-- `sI` is polynomial-time. -/
private theorem polyTimeComputable_sI : PolyTimeComputable sI :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_slot3

/-- `sL` is polynomial-time. -/
private theorem polyTimeComputable_sL : PolyTimeComputable sL := polyTimeComputable_slot4

/-- `sCtx` is polynomial-time. -/
private theorem polyTimeComputable_sCtx : PolyTimeComputable sCtx := polyTimeComputable_pairFstD

/-- `sN` is polynomial-time. -/
private theorem polyTimeComputable_sN : PolyTimeComputable sN :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_sCtx

/-- `sK` is polynomial-time. -/
private theorem polyTimeComputable_sK : PolyTimeComputable sK :=
  polyTimeComputable_add.comp ((polyTimeComputable_slot2.comp polyTimeComputable_sCtx).pairEncode
    (polyTimeComputable_const [true]))

/-- `xW` is polynomial-time. -/
private theorem polyTimeComputable_xW {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    PolyTimeComputable (fun D => xW (f D) D) :=
  polyTimeComputable_getW.comp (hf.pairEncode polyTimeComputable_sL)

/-- `valW` is polynomial-time. -/
private theorem polyTimeComputable_valW : PolyTimeComputable valW := by
  have w := polyTimeComputable_sW
  have h1 : PolyTimeComputable (fun D => xW (arg1W (sW D)) D) :=
    polyTimeComputable_xW (polyTimeComputable_arg1W.comp w)
  have h2 : PolyTimeComputable (fun D => xW (arg2W (sW D)) D) :=
    polyTimeComputable_xW (polyTimeComputable_arg2W.comp w)
  have hpt : PolyTimeComputable (fun D => getW (pairEncode (arg1W (sW D)) (sPts D))) :=
    polyTimeComputable_getW.comp ((polyTimeComputable_arg1W.comp w).pairEncode
      (polyTimeComputable_slot3.comp polyTimeComputable_sCtx))
  have hraw : PolyTimeComputable rawValW :=
    polyTimeComputable_ite (polyTimeComputable_isVarW.comp w)
      (polyTimeComputable_add.comp (hpt.pairEncode (polyTimeComputable_const [true])))
      (polyTimeComputable_ite (polyTimeComputable_isOneW.comp w) (polyTimeComputable_const [true])
        (polyTimeComputable_ite (polyTimeComputable_isAddW.comp w)
          (polyTimeComputable_add.comp (h1.pairEncode h2))
          (polyTimeComputable_ite (polyTimeComputable_isSubW.comp w)
            (polyTimeComputable_add.comp (h1.pairEncode
              (polyTimeComputable_sub.comp (polyTimeComputable_sK.pairEncode h2))))
            (polyTimeComputable_mul.comp (h1.pairEncode h2)))))
  exact polyTimeComputable_mod.comp (hraw.pairEncode polyTimeComputable_sK)

/-- `okW` is polynomial-time.

**Proof sketch.** `okW` is a Boolean combination of the gate-tag tests, the `hasFalse` tests
on the gate's fields and the comparisons `polyTimeComputable_ltLen` of its arguments with
the number of inputs and of earlier nodes. -/
private theorem polyTimeComputable_okW :
    PolyTimeComputable (fun D => [okW (sN D).length (sI D).length (sW D)]) := by
  have w := polyTimeComputable_sW
  have hb : PolyTimeComputable (fun D => [hasFalse (bodyW (sW D))]) :=
    polyTimeComputable_hasFalse.comp (polyTimeComputable_bodyW.comp w)
  have hm : PolyTimeComputable (fun D => [hasFalse (midW (sW D))]) :=
    polyTimeComputable_hasFalse.comp (polyTimeComputable_midW.comp w)
  have hvar : PolyTimeComputable (fun D =>
      [isVarW (sW D) && hasFalse (bodyW (sW D)) &&
        decide ((arg1W (sW D)).length < (sN D).length)]) :=
    polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_isVarW.comp w) hb)
      (polyTimeComputable_ltLen (polyTimeComputable_arg1W.comp w) polyTimeComputable_sN)
  have hbin : PolyTimeComputable (fun D =>
      [(isAddW (sW D) || isSubW (sW D) || isMulW (sW D)) && hasFalse (bodyW (sW D)) &&
        hasFalse (midW (sW D)) && decide ((arg1W (sW D)).length < (sI D).length) &&
        decide ((arg2W (sW D)).length < (sI D).length)]) :=
    polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_and
      (polyTimeComputable_and (polyTimeComputable_or (polyTimeComputable_or
        (polyTimeComputable_isAddW.comp w) (polyTimeComputable_isSubW.comp w))
          (polyTimeComputable_isMulW.comp w)) hb) hm)
      (polyTimeComputable_ltLen (polyTimeComputable_arg1W.comp w) polyTimeComputable_sI))
      (polyTimeComputable_ltLen (polyTimeComputable_arg2W.comp w) polyTimeComputable_sI)
  exact polyTimeComputable_and (polyTimeComputable_headD.comp w)
    (polyTimeComputable_or (polyTimeComputable_or hvar (polyTimeComputable_isOneW.comp w)) hbin)

/-- The word step is polynomial-time. -/
theorem polyTimeComputable_gStep : PolyTimeComputable gStep := by
  have w := polyTimeComputable_sW
  exact polyTimeComputable_ite (polyTimeComputable_isDone.comp w) polyTimeComputable_id
    (polyTimeComputable_ite polyTimeComputable_okW
      (polyTimeComputable_sCtx.pairEncode ((polyTimeComputable_restW.comp w).pairEncode
        (((polyTimeComputable_prepend [true]).comp polyTimeComputable_sI).pairEncode
          (polyTimeComputable_sL.append
            (polyTimeComputable_valW.pairEncode (polyTimeComputable_const []))))))
      (polyTimeComputable_sCtx.pairEncode ((polyTimeComputable_const []).pairEncode
        (polyTimeComputable_sI.pairEncode polyTimeComputable_sL))))

/-- The step keeps the context. -/
theorem pairFstD_gStep (D : List Bool) : pairFstD (gStep D) = pairFstD D := by
  unfold gStep
  split_ifs <;> simp [sCtx]

/-- The rest of the code is no longer than the code. -/
theorem length_restW_le (w : List Bool) : (restW w).length ≤ w.length := by
  have h1 := length_uRest_le (bodyW w)
  have h2 := length_uRest_le (midW w)
  have h3 : (bodyW w).length ≤ w.length := by simp [bodyW]
  unfold restW
  split_ifs <;> simp only [midW, rest2W] at * <;> omega

/-- A value mod `k = R + 1` is no longer than `R`. -/
theorem length_valW_le (D : List Bool) : (valW D).length ≤ (sRaw D).length := by
  unfold valW
  simp only [BinArith.mod, pairFstD_pairEncode, pairSndD_pairEncode, sK, BinArith.add, bitsVal_bits]
  refine length_bits_le_of_le (sRaw D) ?_ le_rfl
  have h1 : bitsVal [true] = 1 := rfl
  rw [h1]
  have := Nat.mod_lt (bitsVal (rawValW D)) (by omega : 0 < bitsVal (sRaw D) + 1)
  omega

/-- The step grows a state by at most `10(|ctx| + 1)`. -/
theorem length_gStep_le (D : List Bool) :
    (gStep D).length ≤ D.length + 10 * ((pairFstD D).length + 1) := by
  have hD := length_pair_components_le D
  have hD2 := length_pair_components_le (pairSndD D)
  have hD3 := length_pair_components_le (pairSndD (pairSndD D))
  have hr := length_restW_le (sW D)
  have hv := length_valW_le D
  have hR : (sRaw D).length ≤ (pairFstD D).length :=
    (length_pairFstD_le _).trans (length_pairSndD_le _)
  unfold gStep
  split_ifs
  · omega
  · simp only [length_pairEncode, List.length_cons, List.length_append, List.length_nil, sCtx,
      sW, sI, sL] at *
    omega
  · simp only [length_pairEncode, List.length_nil, sCtx, sI, sL] at *
    omega

/-! ### The loop -/

/-- The start state on `⟨ctx, G⟩`: counter `G`, code `G`, no values. -/
def gateInit (z : List Bool) : List Bool :=
  pairEncode (pairSndD z) (pairEncode (pairFstD z) (pairEncode (pairSndD z) (pairEncode [] [])))

/-- **The evaluation loop** on `⟨ctx, G⟩`: `|G|` gate steps from the code `G`. -/
def gateRun (z : List Bool) : List Bool := pairSndD (forLoop gStep (gateInit z))

/-- **The evaluation loop is polynomial-time**: the counted loop (`forLoop`) of a
polynomial-time step that keeps the context and grows a state by at most `10(|ctx| + 1)`. -/
theorem polyTimeComputable_gateRun : PolyTimeComputable gateRun := by
  have hinit : PolyTimeComputable gateInit :=
    polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const _)))
  have hloop : PolyTimeComputable (forLoop gStep) :=
    polyTimeComputable_forLoop polyTimeComputable_gStep (10 + 1) 2
      (forLoop_bound_of_ctx 10 pairFstD_gStep length_gStep_le)
  exact polyTimeComputable_pairSndD.comp (hloop.comp hinit)

/-- The loop on `⟨ctx, G⟩` is `|G|` gate steps from `(G, [])`. -/
theorem gateRun_eq (R : List Bool) (P : List (List Bool)) (G : List Bool) :
    gateRun (pairEncode (ctxOf n R P) G) =
      encState (ctxOf n R P) ((absStep n (bitsVal R + 1) (ptVal P))^[G.length] (G, [])).1
        ((absStep n (bitsVal R + 1) (ptVal P))^[G.length] (G, [])).2 := by
  have h0 : gateInit (pairEncode (ctxOf n R P) G) = pairEncode G (encState (ctxOf n R P) G []) := by
    simp [gateInit, encState]
  rw [gateRun, h0, forLoop_pairEncode, pairSndD_pairEncode, iterate_gStep]

/-- On the code of a node list reading earlier nodes only, the loop ends at `[0]` with the
node values mod `k = R + 1`. -/
theorem gateRun_encodeGates (R : List Bool) (P : List (List Bool)) (gs : List (AlgGate n))
    (h : ∀ i (hi : i < gs.length), gs[i].refsBelow i = true) :
    gateRun (pairEncode (ctxOf n R P) (encodeGates gs)) =
      encState (ctxOf n R P) [false] (evalVals (bitsVal R + 1) (ptVal P) gs []) := by
  have hlen := length_encodeGates gs
  have hit := iterate_absStep_encodeGates (bitsVal R + 1) (ptVal P) gs [] (by simpa using h)
  rw [gateRun_eq, show (encodeGates gs).length = ((encodeGates gs).length - gs.length) +
    gs.length by omega, Function.iterate_add_apply, hit, Function.iterate_fixed rfl]

/-- The loop reached the end of a node list. -/
def runOk (D : List Bool) : Bool := !isNilB (sW D) && isDone (sW D)

/-- The value of the last node. -/
def runVal (D : List Bool) : List Bool := getW (pairEncode ((sI D).drop 1) (sL D))

/-- `runOk` on an encoded state: the code is `[0]`. -/
theorem runOk_encState (ctx w : List Bool) (vs : List ℕ) :
    runOk (encState ctx w vs) = decide (w = [false]) := by
  simp only [runOk, sW, encState, pairFstD_pairEncode, pairSndD_pairEncode]
  match w with
  | [] => rfl
  | [b] => cases b <;> rfl
  | _ :: _ :: _ => simp [isDone, isNilB]

/-- `runVal` on an encoded state: the last value. -/
theorem runVal_encState (ctx w : List Bool) (vs : List ℕ) :
    runVal (encState ctx w vs) = Nat.bits (vs.getD (vs.length - 1) 0) := by
  simp only [runVal, sI, sL, encState, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [getW_pairEncode_bits]
  simp

/-- **Only codes of node lists are accepted**: if the loop ends at `[0]`, the code is that of
a node list reading earlier nodes only, and the final state holds its values. -/
theorem exists_of_runOk (R : List Bool) (P : List (List Bool)) (G : List Bool)
    (h : runOk (gateRun (pairEncode (ctxOf n R P) G)) = true) :
    ∃ gs : List (AlgGate n), G = encodeGates gs ∧
      (∀ i (hi : i < gs.length), gs[i].refsBelow i = true) ∧
      gateRun (pairEncode (ctxOf n R P) G) =
        encState (ctxOf n R P) [false] (evalVals (bitsVal R + 1) (ptVal P) gs []) := by
  rw [gateRun_eq, runOk_encState, decide_eq_true_eq] at h
  set s := (absStep n (bitsVal R + 1) (ptVal P))^[G.length] (G, []) with hs
  have hs' : (absStep n (bitsVal R + 1) (ptVal P))^[G.length] (G, []) = ([false], s.2) := by
    rw [← hs, ← h]
  obtain ⟨gs, hG, href, hv⟩ := exists_of_iterate_absStep (bitsVal R + 1) (ptVal P) _ _ _ _ hs'
  refine ⟨gs, hG, by simpa using href, ?_⟩
  rw [gateRun_eq, ← hs, h, hv]

/-! ### Validity and value -/

/-- The leading `1`s are `1`s. -/
theorem uHead_eq_replicate (w : List Bool) : uHead w = List.replicate (uHead w).length true := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [List.replicate_succ, ← ih]

/-- The scan of `x = 1ⁿ0G`: the loop on `G` with `n` inputs, modulus `1` and no point. -/
def scanRun (x : List Bool) : List Bool :=
  gateRun (pairEncode (pairEncode (uHead x) (pairEncode [] [])) (uRest x))

/-- **The word-level validity test**: `x` has a `0`, the loop on the rest accepts, and the
circuit is nonempty. -/
def validW (x : List Bool) : Bool :=
  hasFalse x && runOk (scanRun x) && !isNilB (sI (scanRun x))

/-- The scan context is `ctxOf`. -/
theorem scan_ctx (x : List Bool) :
    pairEncode (uHead x) (pairEncode [] []) = ctxOf (uHead x).length [] [] := by
  rw [ctxOf, ← uHead_eq_replicate]
  rfl

/-- **`validW` decides "`x` encodes a well-formed circuit"** ([AB09, §7.2.3]; the input
condition of `ZEROP`).

**Proof sketch.** A word `x` with a `0` is `1ⁿ0G` with `n = |uHead x|`, `G = uRest x`. If the
scan of `G` ends at `[0]`, `G` is the code of a node list reading earlier nodes only
(`exists_of_runOk`), nonempty since the node counter is nonempty: a well-formed circuit whose
code is `x`. Conversely the code of a well-formed circuit runs to the end
(`gateRun_encodeGates`) with one counter letter per node. -/
theorem validW_iff (x : List Bool) :
    validW x = true ↔ ∃ c : (n : ℕ) × AlgCircuit n, decode x = some c ∧ c.2.WellFormed := by
  constructor
  · intro h
    simp only [validW, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hf, hok⟩, hne⟩ := h
    rw [scanRun, scan_ctx] at hok hne
    obtain ⟨gs, hG, href, hrun⟩ := exists_of_runOk _ _ _ hok
    rw [hrun] at hne
    simp only [sI, encState, pairFstD_pairEncode, pairSndD_pairEncode, length_evalVals,
      List.length_nil, Nat.zero_add, isNilB, decide_eq_false_iff_not] at hne
    refine ⟨⟨(uHead x).length, ⟨gs⟩⟩, ?_, ?_, href⟩
    · rw [decode_eq_some_iff, encode]
      dsimp only
      rw [← hG]
      exact (eq_encodeNat_of_hasFalse hf).symm
    · intro hgs
      apply hne
      change gs = [] at hgs
      simp [hgs]
  · rintro ⟨⟨n, C⟩, hd, hw⟩
    have hx := encode_of_decode hd
    simp only [encode] at hx
    subst hx
    have hrun := gateRun_encodeGates (n := n) [] [] C.gates hw.2
    simp only [validW, scanRun, uHead_encodeNat, uRest_encodeNat, hasFalse_encodeNat]
    rw [show pairEncode (List.replicate n true) (pairEncode [] []) = ctxOf n [] [] from rfl, hrun,
      runOk_encState]
    simp only [sI, encState, pairFstD_pairEncode, pairSndD_pairEncode, length_evalVals,
      List.length_nil, Nat.zero_add, isNilB, decide_true, Bool.true_and, Bool.not_eq_true',
      decide_eq_false_iff_not,
      List.replicate_eq_nil_iff]
    exact (List.length_pos_iff.mpr hw.1).ne'

/-- On a well-formed circuit, the scan counts its nodes. -/
theorem sI_scanRun {x : List Bool} {n : ℕ} {C : AlgCircuit n} (hd : decode x = some ⟨n, C⟩)
    (hw : C.WellFormed) : sI (scanRun x) = List.replicate C.size true := by
  have hx := encode_of_decode hd
  simp only [encode] at hx
  subst hx
  simp only [scanRun, uHead_encodeNat, uRest_encodeNat]
  rw [show pairEncode (List.replicate n true) (pairEncode [] []) = ctxOf n [] [] from rfl,
    gateRun_encodeGates _ _ _ hw.2]
  simp [sI, encState, length_evalVals, size]

/-- The value word of the evaluation loop on `⟨ctx, G⟩`. -/
def evalModW (z : List Bool) : List Bool := runVal (gateRun z)

/-- **Evaluation mod `k`**: for a well-formed circuit `C`, the loop's value is the residue of
`C(a)` modulo `k = R + 1`, where `aᵢ = 1 + P[i]`.  [AB09, §7.2.3, p.130] -/
theorem evalModW_spec {n : ℕ} (R : List Bool) (P : List (List Bool)) (C : AlgCircuit n)
    (hC : C.WellFormed) :
    bitsVal (evalModW (pairEncode (ctxOf n R P) (encodeGates C.gates))) < bitsVal R + 1 ∧
      ((bitsVal (evalModW (pairEncode (ctxOf n R P) (encodeGates C.gates))) : ℕ) :
        ZMod (bitsVal R + 1)) = C.eval (fun i => (ptVal P i : ZMod (bitsVal R + 1))) := by
  have hk : 0 < bitsVal R + 1 := Nat.succ_pos _
  rw [evalModW, gateRun_encodeGates _ _ _ hC.2, runVal_encState, bitsVal_bits,
    length_evalVals, List.length_nil, Nat.zero_add]
  refine ⟨?_, ?_⟩
  · rw [List.getD_eq_getElem?_getD]
    cases hv : (evalVals (bitsVal R + 1) (ptVal P) C.gates [])[C.gates.length - 1]? with
    | none => simp [hk]
    | some v => exact lt_of_mem_evalVals hk _ _ (List.mem_of_getElem? hv)
  · rw [AlgCircuit.eval, ← natCast_evalVals hk, getD_map_natCast]
    rfl

/-- The scan is polynomial-time. -/
theorem polyTimeComputable_scanRun : PolyTimeComputable scanRun := by
  have h1 : PolyTimeComputable (fun x : List Bool =>
      pairEncode (pairEncode (uHead x) (pairEncode [] [])) (uRest x)) :=
    (polyTimeComputable_uHead.pairEncode (polyTimeComputable_const (pairEncode [] []))).pairEncode
      polyTimeComputable_uRest
  have h : scanRun = gateRun ∘ (fun x : List Bool =>
      pairEncode (pairEncode (uHead x) (pairEncode [] [])) (uRest x)) := by
    funext x; simp only [scanRun, Function.comp_apply]
  rw [h]
  exact polyTimeComputable_gateRun.comp h1

/-- `runOk` is polynomial-time. -/
theorem polyTimeComputable_runOk : PolyTimeComputable (fun D => [runOk D]) := by
  have h1 : PolyTimeComputable (fun D => [isNilB (sW D)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_sW
  have h2 : PolyTimeComputable (fun D => [isDone (sW D)]) :=
    polyTimeComputable_isDone.comp polyTimeComputable_sW
  have h : (fun D => [runOk D]) = (fun D => [(!isNilB (sW D)) && isDone (sW D)]) := rfl
  rw [h]
  exact polyTimeComputable_and (polyTimeComputable_not h1) h2

/-- `validW` is polynomial-time. -/
theorem polyTimeComputable_validW : PolyTimeComputable (fun x => [validW x]) := by
  have h1 : PolyTimeComputable (fun x => [runOk (scanRun x)]) :=
    polyTimeComputable_runOk.comp polyTimeComputable_scanRun
  have h2 : PolyTimeComputable (fun D => [isNilB (sI D)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_sI
  have h3 : PolyTimeComputable (fun x => [isNilB (sI (scanRun x))]) :=
    h2.comp polyTimeComputable_scanRun
  have h : (fun x => [validW x]) =
      (fun x => [(hasFalse x && runOk (scanRun x)) && !isNilB (sI (scanRun x))]) := rfl
  rw [h]
  exact polyTimeComputable_and (polyTimeComputable_and polyTimeComputable_hasFalse h1)
    (polyTimeComputable_not h3)

/-- `runVal` is polynomial-time. -/
theorem polyTimeComputable_runVal : PolyTimeComputable runVal := by
  have a : PolyTimeComputable (fun D => (sI D).drop 1) :=
    polyTimeComputable_tail.comp polyTimeComputable_sI
  have hp : PolyTimeComputable (fun D => pairEncode ((sI D).drop 1) (sL D)) :=
    a.pairEncode polyTimeComputable_sL
  have h : runVal = getW ∘ (fun D => pairEncode ((sI D).drop 1) (sL D)) := by
    funext D; simp only [runVal, Function.comp_apply]
  rw [h]
  exact polyTimeComputable_getW.comp hp

/-- `evalModW` is polynomial-time. -/
theorem polyTimeComputable_evalModW : PolyTimeComputable evalModW := by
  have h : evalModW = runVal ∘ gateRun := by
    funext D; simp only [evalModW, Function.comp_apply]
  rw [h]
  exact polyTimeComputable_runVal.comp polyTimeComputable_gateRun

end PIT

end Randomized
