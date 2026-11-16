import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    (yaoAlice Y E₁ E₂).Efficient := by
  obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
  have hdesc n : gen (List.replicate n true) = pairEncode (Y.circ n).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (Y.outs n j))) := by
    simpa only [encodeCircuit_eq, encodeMsgs_eq_encWords] using hgenEq n
  have hfan n (i : Fin (Y.circ n).gates.length) :
      ((Y.circ n).gates[i]).args.length ≤ 2 :=
    ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n) _
      (List.getElem_mem i.isLt)).1.1
  have hN := EncodingMachines.unaryLength_poly GI.argX_poly
  have hA := (polyTimeComputable_unaryPoly Y.inA).comp' GI.argX_poly
  have hB := (polyTimeComputable_unaryPoly Y.inB).comp' GI.argX_poly
  have hp := AliceProgram.message_poly hE₁ hE₂
    (fun w => (GI.argX w).length) (fun w => Y.sizeBound.eval (GI.argX w).length)
    (fun w => Y.inA.eval (GI.argX w).length + Y.inB.eval (GI.argX w).length)
    (fun w => Y.inA.eval (GI.argX w).length) (fun w => Y.outLen.eval (GI.argX w).length)
    (fun w => gen (List.replicate (GI.argX w).length true))
    (fun w => pairFstD (GI.argZ w)) NUPPT.inCoins
    hN ((polyTimeComputable_unaryPoly Y.sizeBound).comp' GI.argX_poly)
    (EncodingMachines.unaryAdd_poly hA hB) hA
    ((polyTimeComputable_unaryPoly Y.outLen).comp' GI.argX_poly)
    (hgen.comp' hN) (polyTimeComputable_pairFstD.comp' GI.argZ_poly)
    NUPPT.polyTimeComputable_inCoins
    (fun w => Y.circ (GI.argX w).length)
    (fun w => yaoSeed Y (GI.argX w).length (NUPPT.inCoins w))
    (fun w => Y.outs (GI.argX w).length) (fun w => hdesc _)
    (fun _ => Nat.le_add_right _ _) (fun w => Y.outs_lt _) (fun w => hfan _)
    (fun w v hv b => by rw [keyAt_yaoSeed Y _ _ hv]; rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  apply firstThenEcho_efficient (yaoAlice Y E₁ E₂)
    (fun x z r => yaoMsg Y E₁ E₂ x.length (pairFstD z) r)
    (yaoAlice_next_nil Y E₁ E₂) (yaoAlice_next_cons Y E₁ E₂)
  refine hp.congr fun w => ?_
  simp only [yaoMsg_eq, yaoTables_eq, yaoKeysA_eq, yaoPairs_eq, encodeMsgs_eq_encWords]

end TCSlib.Cryptography.SecureComputation
