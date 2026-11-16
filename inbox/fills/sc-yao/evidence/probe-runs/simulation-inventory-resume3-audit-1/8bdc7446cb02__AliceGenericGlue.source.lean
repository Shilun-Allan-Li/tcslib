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
  apply AliceStatistical.distAdv_real_ideal_le (yaoHybrid Y E₁ E₂) (yaoFunctionality Y)
    (yaoCoins Y) rfl (yaoMain_rounds Y E₁ E₂) (yaoMain_verifierFirst Y E₁ E₂)
    (fun n q => ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n q) ∧
      ∀ j, keyAt (Y.circ n) (yaoSeed Y n q) (Y.outs n j) false ≠
        keyAt (Y.circ n) (yaoSeed Y n q) (Y.outs n j) true)) δ hWHP (fun _ _ _ => rfl)
  intro n x y r hr
  exact (yaoHybrid_correct Y E₁ E₂ n x y r (not_not.mp hr).1 (not_not.mp hr).2).1

end TCSlib.Cryptography.SecureComputation
