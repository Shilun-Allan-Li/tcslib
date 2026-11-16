import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    (xs ys rA rB : List Bool) (v : ℕ → Bool)
    (hv : ∀ i : Fin (Y.inB.eval n), v (Y.inA.eval n + i) = ys.getD i false) :
    (yaoHybrid Y E₁ E₂).answersB n xs ys rA rB =
      List.ofFn (FakeObjects.activeAnswers (Y.circ n)
        (RelabelGarbling.relabelSeed (Y.circ n) v (yaoSeed Y n rA))
        (Y.inA.eval n) (Y.inB.eval n)) := by
  have hlen : ((yaoHybrid Y E₁ E₂).answersB n xs ys rA rB).length = Y.inB.eval n * n := by
    rw [HybridProtocol.answersB_eq, List.length_flatten, List.map_ofFn]
    change (List.ofFn (fun j : Fin ((yaoHybrid Y E₁ E₂).calls.eval n) =>
      (List.ofFn (otFunctionality.f n ((yaoHybrid Y E₁ E₂).callA n xs rA j)
        ((yaoHybrid Y E₁ E₂).callB n ys rB j)).2).length)).sum = _
    simp only [Function.comp_apply, List.length_ofFn, otFunctionality_outB,
      PolyExpr.eval_const, List.ofFn_const, List.sum_replicate_nat, Nat.mul_one]
    rfl
  have hpoint (j : Fin (Y.inB.eval n * n)) :
      ((yaoHybrid Y E₁ E₂).answersB n xs ys rA rB).getD j false =
        FakeObjects.activeAnswers (Y.circ n)
          (RelabelGarbling.relabelSeed (Y.circ n) v (yaoSeed Y n rA))
          (Y.inA.eval n) (Y.inB.eval n) j := by
    obtain ⟨⟨i, t⟩, rfl⟩ := (finProdFinEquiv (m := Y.inB.eval n) (n := n)).surjective j
    rw [GateHybridMessage.activeAnswers_relabel]
    change _ = keyAt (Y.circ n) (yaoSeed Y n rA)
      (Y.inA.eval n + (finProdFinEquiv.symm (finProdFinEquiv (i, t))).1)
      (v (Y.inA.eval n + (finProdFinEquiv.symm (finProdFinEquiv (i, t))).1))
      (finProdFinEquiv.symm (finProdFinEquiv (i, t))).2
    rw [Equiv.symm_apply_apply, hv]
    have hi : i * n + t = (finProdFinEquiv (i, t) : ℕ) := by
      rw [finProdFinEquiv_apply_val]
      ring
    rw [← hi, yaoHybrid_answersB_getD]
    rfl
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact hlen
  · intro i hi hj
    have h := hpoint ⟨i, by omega⟩
    simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using h

end TCSlib.Cryptography.SecureComputation
