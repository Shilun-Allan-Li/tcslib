import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.SecureComputation.YaoSpecializationProbe

open Complexity Turing BoolCircuit YaoHybridProof

/-- Concrete interface construction only; no Yao semantic object is redefined. -/
noncomputable def data (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (gen : List Bool → List Bool) (hgen : PolyTimeComputable gen)
    (hgenEq : ∀ n, gen (List.replicate n true) = encodeCircuit (Y.circ n) (Y.outs n)) :
    FakeSimulator.Data := by
  refine FakeSimulator.Data.make (E₁ := E₁) (E₂ := E₂) (E₁_poly := hE₁) (E₂_poly := hE₂)
    (bound := Y.sizeBound) (inputs := .add Y.inA Y.inB) (inA := Y.inA) (inB := Y.inB)
    (outLen := Y.outLen) (gen := gen) (gen_poly := hgen) (circuit := Y.circ)
    (output := Y.outs) (shape := ?_) (input_range := ?_) (output_lt := Y.outs_lt)
    (fanin := ?_) (seed := yaoSeed Y) (key := ?_) (nonce₀ := ?_) (nonce₁ := ?_)
    (permutation := ?_)
  · intro n
    simpa only [encodeCircuit_eq, encodeMsgs_eq_encWords] using hgenEq n
  · intro n
    simpa only [PolyExpr.eval_add] using Nat.le_refl (Y.inA.eval n + Y.inB.eval n)
  · intro n i
    exact ((DAGCircuit.isFaninTwo_iff (Y.circ n)).mp (Y.fanin n)).2 _
      (List.getElem_mem i.isLt)
  · intro n r v hv b
    funext t
    rw [keyAt_yaoSeed Y n r hv b, readBits_apply]
  · intro n r i a t
    rw [yaoSeed_snd_fst, readBits_apply, assignIdx_eq]
  · intro n r i a t
    rw [yaoSeed_snd_fst, readBits_apply, assignIdx_eq]
  · intro n r i a t
    rw [yaoSeed_snd_snd, xorShift_apply, readBits_apply]

end TCSlib.Cryptography.SecureComputation.YaoSpecializationProbe
