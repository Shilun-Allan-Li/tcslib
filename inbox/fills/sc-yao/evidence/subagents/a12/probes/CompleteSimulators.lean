import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulatorFactory
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceStatistical
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStatistical
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStageZero
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation.YaoCompleteSimulatorProbe
open Complexity Turing BoolCircuit YaoHybridProof TCSlib.Cryptography

/-- Complete concrete simulator assembly, proved modulo exactly the two authorized frozen
security statements. Owner-local Yao reduction models the future frozen theorem body;
this evidence file changes no frozen source or theorem signature. -/
theorem simulators_complete (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)
    (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
    (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) →
      (Fin ((PolyExpr.add .var innerLen).eval n) → Bool))
    (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₁ n s x))
    (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (G₂ n s x))
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hG₁ : PRFOut (.add .var .var) G₁) (hG₂ : PRFOut (.add .var innerLen) G₂)
    (hG₁₂ : PRFOut (.add (.add .var .var) (.add .var innerLen))
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x))) :
    ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
        (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool),
        distAdv ((yaoHybrid Y E₁ E₂).realA (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv ((yaoHybrid Y E₁ E₂).realB (yaoFunctionality Y) n x y)
            ((yaoFunctionality Y).idealB SB n x y) (D.distinguisherL n) ≤ ε n := by
  classical
  have hFan n (i : Fin (Y.circ n).gates.length) :=
    ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _ (List.getElem_mem i.isLt)
  have hSeedK := yaoSeed_fst Y
  have hSeedR₀ := fun n q i a => congrArg Prod.fst (yaoSeed_snd_fst Y n q i a)
  have hSeedR₁ := fun n q i a => congrArg Prod.snd (yaoSeed_snd_fst Y n q i a)
  obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
  obtain ⟨SB, hSBuniform, hSBcoins, _, hIdeal⟩ := FakeSimulatorFactory.exists_simulator
    (E₁ := E₁) (E₂ := E₂) (E₁_poly := hE₁) (E₂_poly := hE₂)
    (bound := Y.sizeBound) (inputs := .add Y.inA Y.inB) (inA := Y.inA) (inB := Y.inB)
    (outLen := Y.outLen) (gen := gen) (gen_poly := hgen) (circuit := Y.circ)
    (output := Y.outs) (output_lt := Y.outs_lt) (seed := yaoSeed Y) (fanin := hFan)
    (shape := fun n => by
      simpa only [encodeCircuit_eq, encodeMsgs_eq_encWords] using hgenEq n)
    (input_range := fun n => Nat.le_refl (Y.inA.eval n + Y.inB.eval n))
    (key := by intro n q w hw b; funext t; rw [keyAt_eq, dif_pos hw, hSeedK, readBits_apply])
    (nonce₀ := by intro n q i a t; simp only [hSeedR₀, readBits_apply, assignIdx_eq])
    (nonce₁ := by intro n q i a t; simp only [hSeedR₁, readBits_apply, assignIdx_eq])
    (permutation := by
      intro n q i a t; simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply])
    (coins := yaoCoins Y)
  obtain ⟨δ, hδ, hWHP⟩ := yaoSeed_good_whp Y E₁ E₂ G₁ G₂ hGE₁ hGE₂ hG₁ hG₂
  let BadWord n q := ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n q) ∧
    ∀ j, keyAt (Y.circ n) (yaoSeed Y n q) (Y.outs n j) false ≠
      keyAt (Y.circ n) (yaoSeed Y n q) (Y.outs n j) true)
  let switched n x y := fun r : (yaoHybrid Y E₁ E₂).Coins n => pairEncode
    ((yaoHybrid Y E₁ E₂).main.viewV (List.replicate n true)
      ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2))
      ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2)) r).encode
    (List.ofFn ((yaoFunctionality Y).f n x y).1)
  let v n (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool) w :=
    ((Y.circ n).values (Fin.append x y)).getD w false
  let game n x y stage := fun r :
      Fin (10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n) → Bool =>
    GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r))
      (Y.inA.eval n) (Y.inB.eval n) (Y.outLen.eval n) (Y.outs n) (v n x y)
      (List.replicate n true) (List.ofFn y) [] (List.ofFn (Y.output n x y)) stage
  have hAlice := AliceStatistical.distAdv_real_ideal_le (yaoHybrid Y E₁ E₂)
    (yaoFunctionality Y) (yaoCoins Y) rfl (yaoMain_rounds Y E₁ E₂)
    (yaoMain_verifierFirst Y E₁ E₂) BadWord δ hWHP (fun _ _ _ => rfl)
    (fun n x y r hr => (yaoHybrid_correct Y E₁ E₂ n x y r
      (not_not.mp hr).1 (not_not.mp hr).2).1)
  have hSwitch := BobStatistical.statClose_real_output_switch
    (yaoHybrid Y E₁ E₂) (yaoFunctionality Y) (yaoCoins Y) rfl BadWord δ hWHP
    (fun n x y r hr => (yaoHybrid_correct Y E₁ E₂ n x y r
      (not_not.mp hr).1 (not_not.mp hr).2).2)
  -- The joint slice-security consumer supplies the complete computational hybrid.
  have hBob : ∀ D : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n x y,
      distAdv (game n x y 0) (game n x y (2 * (Y.circ n).gates.length))
        (D.distinguisherL n) ≤ μ n := by
    intro D
    obtain ⟨μ, hμ, hBound⟩ := GateHybridSecurity.endpoint_negligible
      (L := .add (.add .var .var) (.add .var innerLen))
      (I := fun n => (Fin (Y.inA.eval n) → Bool) × (Fin (Y.inB.eval n) → Bool))
      Y.circ Y.sizeBound Y.inA Y.inB Y.outLen Y.outLen (yaoSeed Y)
      (fun n z => v n z.1 z.2) Y.outs (fun _ z => List.ofFn z.2)
      (fun n z => List.ofFn (Y.output n z.1 z.2)) Y.size_le Y.fanin
      (fun n z => GateHybrids.values_consistent (Y.circ n) (Fin.append z.1 z.2)) Y.outs_sink
      (fun n z => by simp only [List.length_ofFn, le_refl])
      (fun n z => by simp only [List.length_ofFn, le_refl])
      (fun n s x => Fin.append (G₁ n s x) (G₂ n s x)) G₁ G₂ E₁ E₂ hE₂
      (fun n s x => List.ofFn_fin_append (G₁ n s x) (G₂ n s x)) hGE₁ hGE₂
      (fun n => by
        simp only [PolyExpr.eval_add, innerLen_eq, PolyExpr.eval_mul,
          PolyExpr.eval_const, PolyExpr.eval_var]
        omega)
      (sliceMultiMessageSecure_of_prfOut hG₁₂)
      (fun n q w b t => by rw [hSeedK, readBits_apply])
      (fun n q i a t => by simp only [hSeedR₀, readBits_apply, assignIdx_eq])
      (fun n q i a t => by simp only [hSeedR₁, readBits_apply, assignIdx_eq])
      (fun n q i a t => by simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply]) D
    exact ⟨μ, hμ, fun n x y => hBound n (x, y)⟩
  refine ⟨AliceSimulator.simulator (yaoCoins Y), SB, simulators_of_output_switch
    (yaoHybrid Y E₁ E₂) (yaoFunctionality Y) _ SB switched δ hδ hAlice hSwitch ?_⟩
  intro D; obtain ⟨μ, hμ, hBound⟩ := hBob D
  refine ⟨μ, hμ, ?_⟩; intro n x y
  have hvA (i : Fin (Y.inA.eval n)) : v n x y i = (List.ofFn x).getD i false := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    simpa only [Fin.coe_castAdd, Fin.append_left] using
      (Y.circ n).values_getD_input (Fin.append x y) (Fin.castAdd (Y.inB.eval n) i)
  have hvB (i : Fin (Y.inB.eval n)) : v n x y (Y.inA.eval n + i) =
      (List.ofFn y).getD i false := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    simpa only [Fin.coe_natAdd, Fin.append_right] using
      (Y.circ n).values_getD_input (Fin.append x y) (Fin.natAdd (Y.inA.eval n) i)
  have hStart := BobStageZero.acceptProb_eq_stage0 (Y.circ n) (Y.sizeBound.eval n) n
    (hFan n) (v n x y) (Y.size_le n) (yaoSeed Y n)
    (fun q w b t => by rw [hSeedK, readBits_apply])
    (fun q i a t => by simp only [hSeedR₀, readBits_apply, assignIdx_eq])
    (fun q i a t => by simp only [hSeedR₁, readBits_apply, assignIdx_eq])
    (fun q i a t => by simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply])
    (nestedSpecial E₁ E₂ n) (Y.inA.eval n) (Y.inB.eval n) (Y.outLen.eval n) (Y.outs n)
    (yaoHybrid Y E₁ E₂) (yaoMsg Y E₁ E₂) rfl rfl rfl (yaoAlice_next_nil Y E₁ E₂)
    (List.ofFn x) (List.ofFn y) (List.ofFn ((yaoFunctionality Y).f n x y).1)
    (by rw [Strategy.coinLen_eq, List.length_replicate, yaoHybrid_main, yaoMain_P,
      yaoAlice_coins, yaoCoins_eval])
    (by rw [yaoHybrid_calls, PolyExpr.eval_mul, PolyExpr.eval_var]) hvB
    (fun q r => yaoHybrid_answersB_getD Y E₁ E₂ n _ _ q r)
    (fun r => by simp only [yaoMsg_eq, yaoTables_eq, yaoKeysA_eq, yaoPairs_eq,
      encodeMsgs_eq_encWords, ← hvA]) (D.distinguisherL n)
  let e := (Equiv.arrowCongr (finCongr (yaoCoins_eval Y n).symm) (Equiv.refl Bool)).trans
    (NUPPT.coinsEquivPoly hSBcoins n).symm
  have hEnd := SamplerEndpoints.acceptProb_end_eq_ideal (nestedSpecial E₁ E₂ n) (Y.circ n)
    (fun r => yaoSeed Y n (List.ofFn r)) (Y.inA.eval n) (Y.inB.eval n) (Y.outLen.eval n)
    (Y.outs n) (v n x y) (fun j => (List.ofFn ((yaoFunctionality Y).f n x y).2).getD j false)
    (fun j => by
      change v n x y (Y.outs n j) =
        (List.ofFn ((yaoFunctionality Y).f n x y).2).getD j false
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),
        List.getElem_ofFn]; rfl) (List.replicate n true) (List.ofFn y) []
    (List.ofFn ((yaoFunctionality Y).f n x y).1) e ((yaoFunctionality Y).idealB SB n x y)
    (fun r => by
      simpa only [e, Equiv.trans_apply, NUPPT.coinsEquivPoly_symm_ofFn,
        ofFn_arrowCongr_finCongr] using
        (hIdeal (yaoFunctionality Y) n x y (e r))) (D.distinguisherL n)
  rw [distAdv_def, hStart, ← hEnd]
  have hb := hBound n x y
  rw [distAdv_def] at hb
  exact hb

end TCSlib.Cryptography.SecureComputation.YaoCompleteSimulatorProbe
