/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.StatisticalSwitch
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
# Combining the two simulation bounds

The simulators are fixed before the distinguisher. Alice has a statistical bound;
Bob has the same statistical output switch followed by a computational hybrid bound.
Their sum is one negligible function uniform over the parties' inputs.

## Main definitions

There are no new definitions.

## Main results

* `simulators_of_output_switch`: combine statistical and computational simulation.
* `realB_output_switch`: replace Alice's real output outside a bounded bad event.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 (the two simulators in the OT-hybrid model).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing TCSlib.Cryptography

/-- For fixed simulators `SA`, `SB`, suppose Alice's advantage is bounded by negligible
`δ`, Bob's real experiment is `δ`-close to an output-switched experiment, and that experiment
has a negligible simulation bound for every distinguisher uniformly over the inputs.
Then the same simulators satisfy both simulation clauses with one negligible bound.
[PS10, Theorem 163.7]

**Proof sketch.** For each distinguisher take Bob's uniform hybrid bound. It is nonnegative
at every parameter, since all-false inputs exist and an advantage is nonnegative. Add it
to the statistical bound. Alice's bound only grows; Bob's bound follows from the triangle
inequality between the real, switched and ideal acceptance probabilities. The existing
closure theorem proves the sum negligible. -/
theorem simulators_of_output_switch {G : Functionality} (H : HybridProtocol G)
    (F : Functionality) (SA SB : NUPPT)
    (switched : ∀ n, (Fin (F.inA.eval n) → Bool) → (Fin (F.inB.eval n) → Bool) →
      H.Coins n → List Bool)
    (δ : ℕ → ℝ) (hδ : Negligible δ)
    (hAlice : ∀ (D : NUPPT) n x y,
      distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ δ n)
    (hSwitch : ∀ n x y, StatClose (H.realB F n x y) (switched n x y) (δ n))
    (hBob : ∀ D : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n x y,
      distAdv (switched n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ μ n) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n x y,
      distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
        distAdv (H.realB F n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  intro D
  obtain ⟨μ, hμ, hB⟩ := hBob D
  have hNonneg n : 0 ≤ μ n := by
    have hb := hB n (fun _ => false) (fun _ => false)
    rw [distAdv_def] at hb
    exact (abs_nonneg _).trans hb
  refine ⟨fun n => δ n + μ n, hδ.add hμ, fun n x y => ⟨?_, ?_⟩⟩
  · exact (hAlice D n x y).trans (le_add_of_nonneg_right (hNonneg n))
  · have hs := distAdv_le_of_statClose (H.realB F n x y) (switched n x y)
      (hSwitch n x y) (D.distinguisherL n)
    have hb := hB n x y
    rw [distAdv_def] at hs hb ⊢
    exact (abs_sub_le _ _ _).trans (add_le_add hs hb)

/-- If Alice's actual output equals her functionality output outside a bad event of
probability at most `δ`, Bob's real experiment is `δ`-close to the same encoded view paired
with that functionality output. No change is made to Bob's view or its randomness.
[PS10, Theorem 163.7, Bob's statistical output switch] -/
theorem realB_output_switch {G : Functionality} (H : HybridProtocol G)
    (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (Bad : H.Coins n → Prop) (δ : ℝ)
    (hBad : uprob Bad ≤ δ)
    (hOut : ∀ r, ¬ Bad r →
      H.main.outP (List.replicate n true)
        (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
        (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r =
          List.ofFn (F.f n x y).1) :
    StatClose (H.realB F n x y)
      (fun r => pairEncode
        (H.main.viewV (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
        (List.ofFn (F.f n x y).1)) δ := by
  apply StatisticalSwitch.statClose_of_eq_off _ _ Bad δ hBad
  intro r hr
  rw [HybridProtocol.realB_eq, hOut r hr]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
