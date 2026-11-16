import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool) :
    ∃ B : PolyExpr, ∀ n (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
      (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool)
      (aA : Fin ((yaoHybrid Y E₁ E₂).calls.eval n * otFunctionality.outA.eval n) → Bool)
      (aB : Fin ((yaoHybrid Y E₁ E₂).calls.eval n * otFunctionality.outB.eval n) → Bool)
      (r : (yaoHybrid Y E₁ E₂).Coins n),
      ∀ msg ∈ ((yaoHybrid Y E₁ E₂).main.transcript (List.replicate n true)
          (pairEncode (List.ofFn x) (List.ofFn aA))
          (pairEncode (List.ofFn y) (List.ofFn aB)) r).1 ++
        ((yaoHybrid Y E₁ E₂).main.transcript (List.replicate n true)
          (pairEncode (List.ofFn x) (List.ofFn aA))
          (pairEncode (List.ofFn y) (List.ofFn aB)) r).2,
          msg.length ≤ B.eval n := by
  have hfan n (i : Fin (Y.circ n).gates.length) :
      ((Y.circ n).gates[i]).args.length ≤ 2 :=
    ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
      (List.getElem_mem i.isLt)
  have hLA (w z r : List Bool) :
      (yaoMsg Y E₁ E₂ w.length (pairFstD z) r).length ≤
        (aliceMessageBound Y.sizeBound Y.inA Y.outLen).eval w.length := by
    rw [yaoMsg_eq, aliceMessageBound_eq]
    apply length_message_of_parts_le
    · rw [yaoTables_eq]
      have ht := length_encoded_garbledTables_le E₁ E₂ w.length
        (Y.circ w.length) (yaoSeed Y w.length r) (hfan w.length)
      have hs := Y.size_le w.length
      rw [DAGCircuit.size_eq] at hs
      exact ht.trans (Nat.mul_le_mul_right _ (by omega))
    · rw [yaoKeysA_eq]
      exact length_encoded_keys_le _
    · rw [yaoPairs_eq]
      exact length_encoded_pairs_le _
  have hLB (w z r a : List Bool) :
      (yaoBobOut Y E₁ E₂ w.length a (pairSndD z)).length ≤ Y.outLen.eval w.length := by
    rw [yaoBobOut_eq, List.length_ofFn]
  refine ⟨.add (aliceMessageBound Y.sizeBound Y.inA Y.outLen) Y.outLen, ?_⟩
  intro n x y aA aB r msg hm
  have h := twoMove_message_length_le (yaoMain Y E₁ E₂)
    (fun w z r => yaoMsg Y E₁ E₂ w.length (pairFstD z) r)
    (fun w z _ a => yaoBobOut Y E₁ E₂ w.length a (pairSndD z))
    (yaoMain_rounds Y E₁ E₂) (yaoMain_verifierFirst Y E₁ E₂)
    (fun _ _ _ => yaoAlice_next_nil Y E₁ E₂ _ _ _)
    (fun _ _ _ _ => yaoBob_next Y E₁ E₂ _ _ _ _)
    (aliceMessageBound Y.sizeBound Y.inA Y.outLen) Y.outLen hLA hLB
    (List.replicate n true) (pairEncode (List.ofFn x) (List.ofFn aA))
    (pairEncode (List.ofFn y) (List.ofFn aB)) r msg hm
  simpa only [List.length_replicate] using h

end TCSlib.Cryptography.SecureComputation
