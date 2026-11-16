import TCSlib.Cryptography.SecureComputation.Yao

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

-- This probe is the concrete glue intended for the owned Yao theorem body.
example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) (δ : ℕ → ℝ)
    (hWHP : ∀ n, uprob (fun r : Fin ((yaoCoins Y).eval n) → Bool =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true)) ≤ δ n) :
    ∀ n x y, StatClose ((yaoHybrid Y E₁ E₂).realB (yaoFunctionality Y) n x y)
      (fun r => pairEncode
        ((yaoHybrid Y E₁ E₂).main.viewV (List.replicate n true)
          ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y)
            (List.ofFn r.1) (List.ofFn r.2))
          ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y)
            (List.ofFn r.1) (List.ofFn r.2)) r).encode
        (List.ofFn ((yaoFunctionality Y).f n x y).1)) (δ n) := by
  intro n x y
  let Bad := fun r : (yaoHybrid Y E₁ E₂).Coins n =>
    ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) ∧
      ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) false ≠
        keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) true)
  refine realB_output_switch (yaoHybrid Y E₁ E₂) (yaoFunctionality Y) n x y
    Bad (δ n) ?_ ?_
  · change uprob (fun r : (yaoHybrid Y E₁ E₂).Coins n =>
      ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) ∧
        ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) false ≠
          keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r.1)) (Y.outs n j) true)) ≤ δ n
    rw [uprob_fst (β := (yaoHybrid Y E₁ E₂).main.V.Coins (List.replicate n true).length)
      (fun r : (yaoHybrid Y E₁ E₂).main.P.Coins (List.replicate n true).length =>
        ¬ (Good (nestedSpecial E₁ E₂ n) (Y.circ n) (yaoSeed Y n (List.ofFn r)) ∧
          ∀ j, keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) false ≠
            keyAt (Y.circ n) (yaoSeed Y n (List.ofFn r)) (Y.outs n j) true))]
    have hLen : (yaoHybrid Y E₁ E₂).main.P.coinLen (List.replicate n true).length =
        (yaoCoins Y).eval n := by
      rw [Strategy.coinLen_eq, List.length_replicate]
      rfl
    have h := hWHP n
    rw [← uprob_comp_equiv (strategyTapeEquiv
      (yaoHybrid Y E₁ E₂).main.P (List.replicate n true).length _ hLen)] at h
    simpa only [strategyTapeEquiv_ofFn] using h
  · intro r hr
    exact (yaoHybrid_correct Y E₁ E₂ n x y r (not_not.mp hr).1 (not_not.mp hr).2).2

end TCSlib.Cryptography.SecureComputation
