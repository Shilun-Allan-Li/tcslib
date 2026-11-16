/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs
import TCSlib.Complexity.Randomized.Closure
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
# A polynomial-time Bob simulator from generic fake-garbling interfaces

Two fixed polynomial-time word maps supply a fake garbled message and the active
oblivious-transfer answers. The simulator places them in Bob's encoded view, retaining
his input and an empty private tape. Its machine and coin polynomial are fixed before
any distinguisher is introduced. The leaf contracts are independent of the construction
of a particular fake garbling.

## Main definitions

* `BobSimulator.raw`: the total word map assembling the simulated view.
* `BobSimulator.simulator`: the uniform machine with a supplied coin polynomial.

## Main results

* `BobSimulator.raw_poly`: total polynomial time from the two leaf interfaces.
* `BobSimulator.simulator_uniform`, `simulator_coins`: uniformity and coin budget.
* `BobSimulator.simulator_runAtL`, `simulator_runAt`: exact canonical-layout view contracts.
* `BobSimulator.idealB_eq`: the ideal sampler's exact endpoint, retaining Alice's true output.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (Bob's simulator in the OT-hybrid model).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party
  computation*, Journal of Cryptology 22(2), 2009, pp. 161–188 (one active key per wire).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator

open Complexity Turing TCSlib.Cryptography

/-- Assemble Bob's simulated view
`⟨inParam z, ⟨fst (inArg z), activeAnswers z⟩, [], [fakeMessage z]⟩`.
The prescribed output is available to the leaves as `snd (inArg z)`.
[PS10, Theorem 163.7; LP09] -/
def raw (fakeMessage activeAnswers : List Bool → List Bool) (z : List Bool) : List Bool :=
  (⟨NUPPT.inParam z, pairEncode (pairFstD (NUPPT.inArg z)) (activeAnswers z),
    [], [fakeMessage z]⟩ : View).encode

/-- For every word `z`, `raw fakeMessage activeAnswers z` is the encoded view with
common input `inParam z`, private input `⟨fst (inArg z), activeAnswers z⟩`, empty
private tape and sole received message `fakeMessage z`. -/
theorem raw_eq (fakeMessage activeAnswers : List Bool → List Bool) (z : List Bool) :
    raw fakeMessage activeAnswers z =
      (⟨NUPPT.inParam z, pairEncode (pairFstD (NUPPT.inArg z)) (activeAnswers z),
        [], [fakeMessage z]⟩ : View).encode := rfl

/-- For fixed polynomial-time fake-message and active-answer maps, assembling
Bob's simulated view is polynomial-time on every raw input word.
[PS10, Theorem 163.7] -/
theorem raw_poly {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers) :
    PolyTimeComputable (raw fakeMessage activeAnswers) := by
  have hnil := polyTimeComputable_const ([] : List Bool)
  have hy := polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg
  have hl := NUPPT.polyTimeComputable_inParam.pairEncode (hy.pairEncode hA)
  have hr := hnil.pairEncode (hM.pairEncode hnil)
  refine (hl.pairEncode hr).congr (g := raw fakeMessage activeAnswers) fun z => ?_
  rw [raw_eq, View.encode_mk]
  simp only [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil]

/-- The Bob simulator is the uniform machine for `raw fakeMessage activeAnswers`
with the supplied coin polynomial. Both leaf maps and the coin polynomial are
fixed independently of a distinguisher. [PS10, Theorem 163.7] -/
noncomputable def simulator {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform (raw_poly hM hA) coins

/-- `simulator hM hA coins = ofPolyTimeUniform (raw_poly hM hA) coins`. -/
theorem simulator_eq {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) :
    simulator hM hA coins = NUPPT.ofPolyTimeUniform (raw_poly hM hA) coins := rfl

/-- The fixed-leaf Bob simulator is uniform for every supplied coin polynomial:
`(simulator hM hA coins).Uniform`. -/
theorem simulator_uniform {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) : (simulator hM hA coins).Uniform := by
  rw [simulator_eq]
  exact NUPPT.ofPolyTimeUniform_uniform (raw_poly hM hA) coins

/-- The Bob simulator keeps the supplied coin polynomial:
`(simulator hM hA coins).coins = coins`. -/
theorem simulator_coins {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) : (simulator hM hA coins).coins = coins :=
  (congrArg NUPPT.coins (simulator_eq hM hA coins)).trans
    (NUPPT.coins_ofPolyTimeUniform (raw_poly hM hA) coins)

/-- On parameter `n`, private input `y`, prescribed output `f`, and any tape `r`,
the simulator returns Bob's view with the leaves evaluated at the canonical word
`NUPPT.layout (1^n) ⟨y,f⟩ [] r`. Its private tape field is empty.
[PS10, Theorem 163.7; LP09] -/
theorem simulator_runAtL {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) (n : ℕ) (y f r : List Bool) :
    (simulator hM hA coins).runAtL n (pairEncode y f) r =
      let w := NUPPT.layout (List.replicate n true) (pairEncode y f) [] r
      (⟨List.replicate n true, pairEncode y (activeAnswers w),
        [], [fakeMessage w]⟩ : View).encode := by
  rw [simulator_eq, NUPPT.runAtL_ofPolyTimeUniform, raw_eq]
  simp only [NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.advInput_eq, NUPPT.layout_eq,
    pairFstD_pairEncode, pairSndD_pairEncode]

/-- On a typed simulator tape `r`, the view contract uses the canonical layout
with coin word `List.ofFn r`; the actual tape field in Bob's view remains empty.
[PS10, Theorem 163.7] -/
theorem simulator_runAt {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) (n : ℕ) (y f : List Bool) (r : (simulator hM hA coins).Coins n) :
    (simulator hM hA coins).runAt n (pairEncode y f) r =
      let w := NUPPT.layout (List.replicate n true) (pairEncode y f) [] (List.ofFn r)
      (⟨List.replicate n true, pairEncode y (activeAnswers w),
        [], [fakeMessage w]⟩ : View).encode := by
  rw [NUPPT.runAt_eq, simulator_runAtL]

/-- Bob's ideal sampler is the simulated view from input `y` and prescribed output
`(F.f n x y).2`, paired with the actual Alice output `(F.f n x y).1`. The leaves
receive only the canonical layout of Bob's input, prescribed output and simulator coins.
[PS10, Theorem 163.7]

This is an endpoint identity, independent of any distinguisher or hybrid argument. -/
theorem idealB_eq {fakeMessage activeAnswers : List Bool → List Bool}
    (hM : PolyTimeComputable fakeMessage) (hA : PolyTimeComputable activeAnswers)
    (coins : PolyExpr) (F : Functionality) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
    (r : (simulator hM hA coins).Coins n) :
    F.idealB (simulator hM hA coins) n x y r =
      let w := NUPPT.layout (List.replicate n true)
        (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) [] (List.ofFn r)
      pairEncode
        (⟨List.replicate n true, pairEncode (List.ofFn y) (activeAnswers w),
          [], [fakeMessage w]⟩ : View).encode
        (List.ofFn (F.f n x y).1) := by
  rw [Functionality.idealB_eq, simulator_runAt]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobSimulator
