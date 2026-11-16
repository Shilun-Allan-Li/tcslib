import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography BoolCircuit YaoHybridProof

example (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    (yaoBob Y E₁ E₂).Efficient := by
  obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
  have hdesc n : gen (List.replicate n true) = pairEncode (Y.circ n).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (Y.outs n j))) := by
    simpa only [encodeCircuit_eq, encodeMsgs_eq_encWords] using hgenEq n
  let msg := fun w => pairFstD (GI.argM w)
  let ans := fun w => pairSndD (GI.argZ w)
  have hp := BobProgram.output_poly Y.inA Y.inB Y.outLen Y.circ Y.outs Y.outs_lt
    hgen hdesc hE₁ hE₂ GI.argX_poly
    (polyTimeComputable_pairFstD.comp' GI.argM_poly)
    (polyTimeComputable_pairSndD.comp' GI.argZ_poly)
    (fun w => yaoBobInit Y (GI.argX w).length (msg w) (ans w))
    (fun w => yaoBobTables Y (GI.argX w).length (msg w))
    (fun w => decodeMsgs (pairSndD (pairSndD (msg w))))
    (fun w => by
      dsimp only
      rw [BobInit.initWords_layout, yaoBobInit_eq, List.map_ofFn]
      simp only [List.length_replicate]
      apply congrArg BinArith.encWords
      apply congrArg List.ofFn
      funext v
      split_ifs <;> rfl)
    (fun w => by simp only [yaoBobInit_eq, List.length_ofFn])
    (fun w v => by simp only [yaoBobTables_eq]; rfl) (fun _ => rfl)
  apply reply_efficient (yaoBob Y E₁ E₂)
    (fun x z a => yaoBobOut Y E₁ E₂ x.length a (pairSndD z))
    (yaoBob_next Y E₁ E₂)
  refine hp.congr fun w => ?_
  simp only [yaoBobOut_eq, yaoBobValues_eq, decodeOut_eq, msg, ans]

end TCSlib.Cryptography.SecureComputation
