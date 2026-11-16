import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulatorFactory
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths
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

namespace TCSlib.Cryptography.SecureComputation.YaoSpecializationProbe
open Complexity Turing BoolCircuit YaoHybridProof

/-- Concrete specialization of the generic factory; no Yao semantic object is redefined. -/
theorem exists_fixedSB (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    ∃ SB : NUPPT, SB.Uniform ∧ SB.coins = yaoCoins Y ∧ ∀ n,
      ∃ e : (Fin (10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n) → Bool) ≃ SB.Coins n,
        (∀ r, List.ofFn (e r) = List.ofFn r) ∧
        ∀ (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
          (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool) r,
        (yaoFunctionality Y).idealB SB n x y (e r) =
          pairEncode
            (⟨List.replicate n true, pairEncode (List.ofFn y)
              (List.ofFn (FakeObjects.activeAnswers (Y.circ n) (yaoSeed Y n (List.ofFn r))
                (Y.inA.eval n) (Y.inB.eval n))), [],
              [FakeObjects.message (nestedSpecial E₁ E₂ n) (Y.circ n)
                (yaoSeed Y n (List.ofFn r)) (Y.inA.eval n) (Y.outLen.eval n) (Y.outs n)
                (fun j => (List.ofFn ((yaoFunctionality Y).f n x y).2).getD j false)]⟩ :
              View).encode
            (List.ofFn ((yaoFunctionality Y).f n x y).1) := by
  obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
  have hFactory := FakeSimulatorFactory.exists_simulator
    (E₁ := E₁) (E₂ := E₂) (E₁_poly := hE₁) (E₂_poly := hE₂)
    (bound := Y.sizeBound) (inputs := .add Y.inA Y.inB) (inA := Y.inA) (inB := Y.inB)
    (outLen := Y.outLen) (gen := gen) (gen_poly := hgen) (circuit := Y.circ)
    (output := Y.outs) (output_lt := Y.outs_lt) (seed := yaoSeed Y)
    (shape := by
      intro n
      simpa only [encodeCircuit_eq, encodeMsgs_eq_encWords] using hgenEq n)
    (input_range := by
      intro n
      simpa only [PolyExpr.eval_add] using Nat.le_refl (Y.inA.eval n + Y.inB.eval n))
    (fanin := by
      intro n i
      exact ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
        (List.getElem_mem i.isLt))
    (key := by
      intro n r v hv b
      funext t
      rw [keyAt_yaoSeed Y n r hv b, readBits_apply])
    (nonce₀ := by
      intro n r i a t
      simp only [yaoSeed_snd_fst, readBits_apply, assignIdx_eq])
    (nonce₁ := by
      intro n r i a t
      simp only [yaoSeed_snd_fst, readBits_apply, assignIdx_eq])
    (permutation := by
      intro n r i a t
      simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply])
    (coins := yaoCoins Y)
  obtain ⟨SB, hU, hC, hRun, hIdeal⟩ := hFactory
  have hLen n : SB.coinLen n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n := by
    rw [NUPPT.coinLen_eq, hC, yaoCoins_eval]
  let e n : (Fin (10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n) → Bool) ≃
      SB.Coins n := Equiv.arrowCongr (finCongr (hLen n).symm) (Equiv.refl Bool)
  have he n r : List.ofFn (e n r) = List.ofFn r :=
    ofFn_arrowCongr_finCongr (hLen n).symm r
  refine ⟨SB, hU, hC, ?_⟩
  intro n
  refine ⟨e n, he n, ?_⟩
  intro x y r
  have h := hIdeal (yaoFunctionality Y) n x y (e n r)
  simpa only [he n r] using h

end TCSlib.Cryptography.SecureComputation.YaoSpecializationProbe
