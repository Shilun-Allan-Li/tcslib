import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStageZero
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
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
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

namespace TCSlib.Cryptography.SecureComputation.YaoGenericStageZeroProbe
open Complexity Turing BoolCircuit YaoHybridProof TCSlib.Cryptography

/-- The generic endpoint specializes to the actual Yao view and wire values. -/
theorem acceptProb_switched_stage0 (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) (α : List Bool)
    {κ : Type*} [Fintype κ] (D : List Bool → κ → Bool) :
    acceptProb (fun r : (yaoHybrid Y E₁ E₂).Coins n =>
      pairEncode
        ((yaoHybrid Y E₁ E₂).main.viewV (List.replicate n true)
          ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y)
            (List.ofFn r.1) (List.ofFn r.2))
          ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y)
            (List.ofFn r.1) (List.ofFn r.2)) r).encode α) D =
    acceptProb (fun r : Fin (10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n) → Bool =>
      GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (Y.circ n)
        (yaoSeed Y n (List.ofFn r)) (Y.inA.eval n) (Y.inB.eval n) (Y.outLen.eval n)
        (Y.outs n) (fun w => ((Y.circ n).values (Fin.append x y)).getD w false)
        (List.replicate n true) (List.ofFn y) [] α 0) D := by
  let v : ℕ → Bool := fun w => ((Y.circ n).values (Fin.append x y)).getD w false
  have hvA (i : Fin (Y.inA.eval n)) : v i = (List.ofFn x).getD i false := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    simpa only [Fin.coe_castAdd, Fin.append_left] using
      (Y.circ n).values_getD_input (Fin.append x y) (Fin.castAdd (Y.inB.eval n) i)
  apply BobStageZero.acceptProb_eq_stage0 (Y.circ n) (Y.sizeBound.eval n) n
    (fun i => ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
      (List.getElem_mem i.isLt)) v (Y.size_le n) (yaoSeed Y n)
    (fun q w b t => by rw [yaoSeed_fst, readBits_apply])
    (fun q i a t => by simp only [yaoSeed_snd_fst, readBits_apply, assignIdx_eq])
    (fun q i a t => by simp only [yaoSeed_snd_fst, readBits_apply, assignIdx_eq])
    (fun q i a t => by simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply])
    (nestedSpecial E₁ E₂ n) (Y.inA.eval n) (Y.inB.eval n) (Y.outLen.eval n) (Y.outs n)
    (yaoHybrid Y E₁ E₂) (yaoMsg Y E₁ E₂)
    (by rw [yaoHybrid_main, yaoMain_rounds])
    (by rw [yaoHybrid_main, yaoMain_verifierFirst])
    (by rw [yaoHybrid_main, yaoMain_V, yaoBob_coins])
    (by intro w z q; rw [yaoHybrid_main, yaoMain_P, yaoAlice_next_nil])
    (List.ofFn x) (List.ofFn y) α
    (by rw [Strategy.coinLen_eq, yaoHybrid_main, yaoMain_P, yaoAlice_coins,
      List.length_replicate, yaoCoins_eval])
    (by rw [yaoHybrid_calls, PolyExpr.eval_mul, PolyExpr.eval_var]) _
    (fun q r => yaoHybrid_answersB_getD Y E₁ E₂ n _ _ q r) _ D
  · intro i
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    simpa only [Fin.coe_natAdd, Fin.append_right] using
      (Y.circ n).values_getD_input (Fin.append x y) (Fin.natAdd (Y.inA.eval n) i)
  · intro r
    simp only [yaoMsg_eq, yaoTables_eq, yaoKeysA_eq, yaoPairs_eq,
      encodeMsgs_eq_encWords, ← hvA]

end TCSlib.Cryptography.SecureComputation.YaoGenericStageZeroProbe
