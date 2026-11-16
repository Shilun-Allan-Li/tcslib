import TCSlib.Cryptography.SecureComputation.Yao

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) (δ : ℕ → ℝ)
    (hWHP : ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n) :
    ∀ (D : NUPPT) n x y,
      distAdv ((yaoHybrid Y E₁ E₂).realA (yaoFunctionality Y) n x y)
        ((yaoFunctionality Y).idealA (AliceSimulator.simulator (yaoCoins Y)) n x y)
        (D.distinguisherL n) ≤ δ n := by
  intro D n x y
  let H := yaoHybrid Y E₁ E₂
  let σ := H.main.P.Coins (List.replicate n true).length
  have hLen : H.main.P.coinLen (List.replicate n true).length = (yaoCoins Y).eval n := by
    rw [Strategy.coinLen_eq, List.length_replicate]
    rfl
  let e₀ : σ ≃ (Fin ((yaoCoins Y).eval n) → Bool) :=
    Equiv.arrowCongr (finCongr hLen) (Equiv.refl Bool)
  let e := e₀.trans (NUPPT.coinsEquivPoly (AliceSimulator.simulator_coins (yaoCoins Y)) n).symm
  have he₀ (r : σ) : List.ofFn (e₀ r) = List.ofFn r :=
    ofFn_arrowCongr_finCongr hLen r
  have he (r : σ) : List.ofFn (e r) = List.ofFn r := by
    rw [Equiv.trans_apply, NUPPT.coinsEquivPoly_symm_ofFn, he₀]
  let Bad := fun r : σ =>
    ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
      ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
        keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)
  have hBad : uprob Bad ≤ δ n := by
    have h := hWHP n
    rw [← uprob_comp_equiv e₀] at h
    simpa only [he₀] using h
  apply AliceSimulator.distAdv_real_ideal_le (yaoCoins Y) (yaoFunctionality Y) n x y
    e (H.realA (yaoFunctionality Y) n x y) Bad (δ n) hBad
  intro r hr
  have hg := not_not.mp hr
  have hv := (yaoHybrid_correct Y E₁ E₂ n x y r hg.1 hg.2).1
  have hNil : H.answersA n (List.ofFn x) (List.ofFn y)
      (List.ofFn r.1) (List.ofFn r.2) = [] := by
    rw [HybridProtocol.answersA_eq]
    apply List.flatten_eq_nil_iff.mpr
    intro word hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    apply List.eq_nil_of_length_eq_zero
    simp only [List.length_ofFn, otFunctionality_outA, PolyExpr.eval_const]
  change (yaoMain Y E₁ E₂).outV (yaoMain Y E₁ E₂).P _ _ _ r = _ at hv
  rw [yaoMain_outV, HybridProtocol.pairFstD_privA, HybridProtocol.pairSndD_privB] at hv
  rw [TwoMoveViews.realA_eq
    (fun w z r => yaoMsg Y E₁ E₂ w.length (pairFstD z) r)
    (fun w z _ a => yaoBobOut Y E₁ E₂ w.length a (pairSndD z)) H
    (yaoMain_rounds Y E₁ E₂) (yaoMain_verifierFirst Y E₁ E₂)
    (yaoAlice_next_nil Y E₁ E₂) (fun _ _ _ _ => yaoBob_next Y E₁ E₂ _ _ _ _)]
  simp only [HybridProtocol.pairSndD_privB, HybridProtocol.privA_eq, hNil,
    pairFstD_pairEncode, View.encode_mk, he]
  rw [hv]
  rfl

end TCSlib.Cryptography.SecureComputation
