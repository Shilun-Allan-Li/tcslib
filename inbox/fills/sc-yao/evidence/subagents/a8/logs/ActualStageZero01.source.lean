import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SamplerEndpoints
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobViewShape
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.OTAnswerWords
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SimulationBound
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation.YaoStageZeroProbe
open Complexity Turing BoolCircuit YaoHybridProof TCSlib.Cryptography

/-- The actual receiver view has the wire-value-selected real payload shape. -/
theorem view_selected (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    (x : Fin (Y.inA.eval n) → Bool) (y : Fin (Y.inB.eval n) → Bool)
    (r : (yaoHybrid Y E₁ E₂).Coins n) :
    ((yaoHybrid Y E₁ E₂).main.viewV (List.replicate n true)
      ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2))
      ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2)) r).encode =
    (⟨List.replicate n true,
      pairEncode (List.ofFn y) (List.ofFn fun t : Fin (Y.inB.eval n * n) =>
        keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.inA.eval n + t.divNat)
          ((Y.circ n).values (Fin.append x y) |>.getD (Y.inA.eval n + t.divNat) false)
          t.modNat), [],
      [yaoMsg Y E₁ E₂ n (List.ofFn x) (List.ofFn r.1)]⟩ : View).encode := by
  let v : ℕ → Bool := fun w => ((Y.circ n).values (Fin.append x y)).getD w false
  have hvB (i : Fin (Y.inB.eval n)) : v (Y.inA.eval n + i) =
      (List.ofFn y).getD i false := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    simpa only [Fin.coe_natAdd, Fin.append_right] using
      (Y.circ n).values_getD_input (Fin.append x y) (Fin.natAdd (Y.inA.eval n) i)
  have hAns := OTAnswerWords.answersB_eq_active (yaoHybrid Y E₁ E₂) n
    (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)
    (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.inA.eval n) (Y.inB.eval n) v
    (by rw [yaoHybrid_calls, PolyExpr.eval_mul, PolyExpr.eval_var]) hvB
    (yaoHybrid_answersB_getD Y E₁ E₂ n _ _ _ _)
  have hView := BobViewShape.encode_viewV_eq (yaoHybrid Y E₁ E₂) (yaoMsg Y E₁ E₂)
    (by rw [yaoHybrid_main, yaoMain_rounds])
    (by rw [yaoHybrid_main, yaoMain_verifierFirst])
    (by rw [yaoHybrid_main, yaoMain_V, yaoBob_coins])
    (by intro w z q; rw [yaoHybrid_main, yaoMain_P, yaoAlice_next_nil])
    n (List.ofFn x) (List.ofFn y) r
  rw [hView, hAns, GateHybridMessage.activeAnswers_relabel]

end TCSlib.Cryptography.SecureComputation.YaoStageZeroProbe
