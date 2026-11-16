import TCSlib.Cryptography.SecureComputation.Yao

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) (n : ℕ)
    (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
    (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool)
    (r : (yaoHybrid Y E₁ E₂).Coins n) :
    ((yaoHybrid Y E₁ E₂).main.viewV (List.replicate n true)
      ((yaoHybrid Y E₁ E₂).privA n (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2))
      ((yaoHybrid Y E₁ E₂).privB n (List.ofFn x) (List.ofFn y)
        (List.ofFn r.1) (List.ofFn r.2)) r).encode =
      (⟨List.replicate n true,
        pairEncode (List.ofFn y) ((yaoHybrid Y E₁ E₂).answersB n (List.ofFn x)
          (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)), [],
        [yaoMsg Y E₁ E₂ n (List.ofFn x) (List.ofFn r.1)]⟩ : View).encode := by
  have hBob : List.ofFn r.2 = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_ofFn]
    change (yaoBob Y E₁ E₂).coinLen (List.replicate n true).length = 0
    rw [Strategy.coinLen_eq, yaoBob_coins, PolyExpr.eval_const]
  have hMsg : yaoMsg Y E₁ E₂ (List.replicate n true).length (List.ofFn x) (List.ofFn r.1) =
      yaoMsg Y E₁ E₂ n (List.ofFn x) (List.ofFn r.1) :=
    congrArg (fun k => yaoMsg Y E₁ E₂ k (List.ofFn x) (List.ofFn r.1))
      (List.length_replicate (n := n) (a := true))
  change ((yaoMain Y E₁ E₂).viewV _ _ _ r).encode = _
  rw [TwoMoveViews.encode_viewV_eq (yaoMain Y E₁ E₂)
    (fun w z r => yaoMsg Y E₁ E₂ w.length (pairFstD z) r)
    (fun w z _ a => yaoBobOut Y E₁ E₂ w.length a (pairSndD z))
    (yaoMain_rounds Y E₁ E₂) (yaoMain_verifierFirst Y E₁ E₂)
    (yaoAlice_next_nil Y E₁ E₂) (fun _ _ _ _ => yaoBob_next Y E₁ E₂ _ _ _ _)]
  simp only [HybridProtocol.pairFstD_privA, hMsg, hBob, HybridProtocol.privB_eq,
    View.encode_mk]

end TCSlib.Cryptography.SecureComputation
