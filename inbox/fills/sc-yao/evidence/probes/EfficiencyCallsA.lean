import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) :
    ∀ n (x r : List Bool) (j : Fin ((yaoHybrid Y E₁ E₂).calls.eval n)),
      OTInputs.otInputA Y.inA Y.sizeBound (pairEncode (List.replicate n true)
        (pairEncode x (pairEncode r (List.replicate j true)))) =
          List.ofFn ((yaoHybrid Y E₁ E₂).callA n x r j) := by
  intro n x r j
  have hlen : otFunctionality.inA.eval n = 2 := by
    rw [otFunctionality_inA, PolyExpr.eval_const]
  rw [List.ofFn_congr hlen]
  apply CallEquations.inputA_eq Y.inA Y.sizeBound n (Y.inB.eval n) x r
  intro i t c
  rw [yaoHybrid_callA, yaoCall_finProdFinEquiv]
  rw [keyAt_yaoSeed Y n r (by
    rw [DAGCircuit.size_eq]
    have := i.isLt
    omega), readBits_apply]
  simp only [Nat.add_assoc]

end TCSlib.Cryptography.SecureComputation
