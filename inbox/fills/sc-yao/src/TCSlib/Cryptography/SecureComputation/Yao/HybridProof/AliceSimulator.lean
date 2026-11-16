/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.StatisticalSwitch
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A copying simulator for an Alice-first two-message view

The simulator constructs the view `⟨1^n, ⟨input, []⟩, coins, [output]⟩` using only
its own input, prescribed output and random tape. Its polynomial-time raw machine
works on every string. A generic coupling contract compares any real sampler with
this ideal sampler when the two agree outside a bad event in Alice's coins.

## Main definitions

* `raw`: the all-input word function constructing the encoded view.
* `simulator`: the uniform machine for `raw`, with a supplied coin polynomial.

## Main results

* `polyTimeComputable_raw`: constructing the view is polynomial-time on every word.
* `simulator_uniform`, `simulator_coins`, `simulator_runAtL`: the machine contracts.
* `statClose_real_ideal`: an off-bad real-view identity gives statistical simulation.
* `distAdv_real_ideal_le`: every randomized distinguisher inherits that bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (Alice's simulator in the OT-hybrid model).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator

open Complexity Turing TCSlib.Cryptography

/-- The raw copying simulator returns the encoding of
`⟨inParam z, ⟨fst (inArg z), []⟩, inCoins z, [snd (inArg z)]⟩`.
It reads no circuit and makes no ideal calls. [PS10, Theorem 163.7] -/
def raw (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairEncode (pairFstD (NUPPT.inArg z)) []))
    (pairEncode (NUPPT.inCoins z) (Strategy.encodeMsgs [pairSndD (NUPPT.inArg z)]))

/-- `raw z = ⟨⟨inParam z, ⟨fst (inArg z), []⟩⟩,
⟨inCoins z, encodeMsgs [snd (inArg z)]⟩⟩`. -/
theorem raw_eq (z : List Bool) :
    raw z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairEncode (pairFstD (NUPPT.inArg z)) []))
        (pairEncode (NUPPT.inCoins z) (Strategy.encodeMsgs [pairSndD (NUPPT.inArg z)])) := rfl

/-- The raw view-copying function is polynomial-time on every string:
`PolyTimeComputable raw`. [PS10, Theorem 163.7] -/
theorem polyTimeComputable_raw : PolyTimeComputable raw := by
  have hnil := polyTimeComputable_const ([] : List Bool)
  have hx := polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hf := polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hleft := NUPPT.polyTimeComputable_inParam.pairEncode (hx.pairEncode hnil)
  have hright := NUPPT.polyTimeComputable_inCoins.pairEncode (hf.pairEncode hnil)
  refine (hleft.pairEncode hright).congr fun z => ?_
  simp only [Function.comp_apply, raw_eq, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil]

/-- The uniform copying simulator uses the supplied polynomial number of coins:
`simulator coins = NUPPT.ofPolyTimeUniform polyTimeComputable_raw coins`.
[PS10, Theorem 163.7] -/
noncomputable def simulator (coins : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_raw coins

/-- `simulator coins = NUPPT.ofPolyTimeUniform polyTimeComputable_raw coins`. -/
theorem simulator_eq (coins : PolyExpr) :
    simulator coins = NUPPT.ofPolyTimeUniform polyTimeComputable_raw coins := rfl

/-- `simulator coins` is uniform for every coin polynomial `coins`. -/
theorem simulator_uniform (coins : PolyExpr) : (simulator coins).Uniform := by
  rw [simulator_eq]
  exact NUPPT.ofPolyTimeUniform_uniform polyTimeComputable_raw coins

/-- The simulator keeps the supplied coin polynomial: `(simulator coins).coins = coins`. -/
theorem simulator_coins (coins : PolyExpr) : (simulator coins).coins = coins := by
  rw [simulator_eq]
  exact NUPPT.coins_ofPolyTimeUniform polyTimeComputable_raw coins

/-- On every parameter `n`, input `x`, prescribed output `f` and tape `r`,
`simulator coins` returns `View.encode ⟨1^n, ⟨x, []⟩, r, [f]⟩`.
The equation holds for arbitrary word lengths. [PS10, Theorem 163.7] -/
theorem simulator_runAtL (coins : PolyExpr) (n : ℕ) (x f r : List Bool) :
    (simulator coins).runAtL n (pairEncode x f) r =
      (⟨List.replicate n true, pairEncode x [], r, [f]⟩ : View).encode := by
  rw [simulator_eq, NUPPT.runAtL_ofPolyTimeUniform, raw_eq, View.encode_mk]
  simp only [NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode]

/-- Given a coin equivalence `e` to the simulator's tape, a real sampler on
`σ × τ` that equals the encoded simulated Alice view paired with `fB` outside
`Bad` is `δ`-close to `F.idealA (simulator coins) n x y` when `Pr[Bad] ≤ δ`.
The simulator is fixed by `coins`, independently of the inputs and distinguisher.
[PS10, Theorem 163.7]

**Proof sketch.** Lift the bad event to the joint coin space; its probability is
unchanged by the independent second tape. The simulator run contract identifies
the ideal sample with the given real-view expression outside this event. Apply
the same-coins statistical switch, then remove the unused second tape and
transport the first tape by the supplied coin equivalence. -/
theorem statClose_real_ideal (coins : PolyExpr) (F : Functionality) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
    {σ τ : Type*} [Fintype σ] [Fintype τ] [Nonempty τ]
    (e : σ ≃ (simulator coins).Coins n) (real : σ × τ → List Bool)
    (Bad : σ → Prop) (δ : ℝ) (hBad : uprob Bad ≤ δ)
    (hReal : ∀ r, ¬ Bad r.1 → real r =
      pairEncode (⟨List.replicate n true, pairEncode (List.ofFn x) [],
        List.ofFn (e r.1), [List.ofFn (F.f n x y).1]⟩ : View).encode
        (List.ofFn (F.f n x y).2)) :
    StatClose real (F.idealA (simulator coins) n x y) δ := by
  classical
  have hBad' : uprob (fun r : σ × τ => Bad r.1) ≤ δ := by
    rw [uprob_fst]
    exact hBad
  have h : StatClose real
      (fun r : σ × τ => F.idealA (simulator coins) n x y (e r.1)) δ :=
    StatisticalSwitch.statClose_of_eq_off real _ (fun r => Bad r.1) δ hBad' fun r hr => by
      rw [hReal r hr, Functionality.idealA_eq, NUPPT.runAt_eq, simulator_runAtL]
  rw [statClose_iff] at h ⊢
  intro T
  have hT := h T
  rw [uprob_fst (β := τ) (fun t : σ => T (F.idealA (simulator coins) n x y (e t))),
    uprob_comp_equiv e (fun t => T (F.idealA (simulator coins) n x y t))] at hT
  exact hT

/-- Under the off-bad real-view identity and `Pr[Bad] ≤ δ`, every randomized
`D` has `distAdv real (F.idealA (simulator coins) n x y) D ≤ δ`.
The same machine `simulator coins` works for all inputs and all distinguishers.
[PS10, Theorem 163.7] -/
theorem distAdv_real_ideal_le (coins : PolyExpr) (F : Functionality) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
    {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Nonempty τ] [Fintype ρ]
    (e : σ ≃ (simulator coins).Coins n) (real : σ × τ → List Bool)
    (Bad : σ → Prop) (δ : ℝ) (hBad : uprob Bad ≤ δ)
    (hReal : ∀ r, ¬ Bad r.1 → real r =
      pairEncode (⟨List.replicate n true, pairEncode (List.ofFn x) [],
        List.ofFn (e r.1), [List.ofFn (F.f n x y).1]⟩ : View).encode
        (List.ofFn (F.f n x y).2)) (D : List Bool → ρ → Bool) :
    distAdv real (F.idealA (simulator coins) n x y) D ≤ δ :=
  distAdv_le_of_statClose real _ (statClose_real_ideal coins F n x y e real Bad δ hBad hReal) D

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator
