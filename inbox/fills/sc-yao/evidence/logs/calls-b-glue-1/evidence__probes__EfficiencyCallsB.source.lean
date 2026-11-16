import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) :
    ∀ n (x r : List Bool) (j : Fin ((yaoHybrid Y E₁ E₂).calls.eval n)),
      OTInputs.otInputB (pairEncode (List.replicate n true)
        (pairEncode x (pairEncode r (List.replicate j true)))) =
          List.ofFn ((yaoHybrid Y E₁ E₂).callB n x r j) := by
  intro n x r j
  have hlen : otFunctionality.inB.eval n = 1 := by
    rw [otFunctionality_inB, PolyExpr.eval_const]
  rw [List.ofFn_congr hlen]
  apply CallEquations.inputB_eq n (Y.inB.eval n) x r
  intro i t c
  rw [yaoHybrid_callB, yaoCall_finProdFinEquiv]

end TCSlib.Cryptography.SecureComputation
