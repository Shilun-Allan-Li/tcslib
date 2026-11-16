import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulator
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths

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
    simp only [yaoSeed_snd_fst, readBits_apply, assignIdx_eq]
  · intro n r i a t
    simp only [yaoSeed_snd_fst, readBits_apply, assignIdx_eq]
  · intro n r i a t
    simp only [yaoSeed_snd_snd, xorShift_apply, readBits_apply]

/-- The concrete fixed simulator's actual ideal endpoint, without unfolding Yao semantics. -/
theorem ideal_eq (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (gen : List Bool → List Bool) (hgen : PolyTimeComputable gen)
    (hgenEq : ∀ n, gen (List.replicate n true) = encodeCircuit (Y.circ n) (Y.outs n))
    (n : ℕ) (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
    (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool)
    (r : (FakeSimulator.simulator (data Y E₁ E₂ hE₁ hE₂ gen hgen hgenEq)
      (yaoCoins Y)).Coins n) :
    (yaoFunctionality Y).idealB
        (FakeSimulator.simulator (data Y E₁ E₂ hE₁ hE₂ gen hgen hgenEq) (yaoCoins Y))
        n x y r =
      pairEncode
        (⟨List.replicate n true, pairEncode (List.ofFn y)
          (List.ofFn (FakeObjects.activeAnswers (Y.circ n) (yaoSeed Y n (List.ofFn r))
            (Y.inA.eval n) (Y.inB.eval n))), [],
          [FakeObjects.message (nestedSpecial E₁ E₂ n) (Y.circ n)
            (yaoSeed Y n (List.ofFn r)) (Y.inA.eval n) (Y.outLen.eval n) (Y.outs n)
            (fun j => (List.ofFn ((yaoFunctionality Y).f n x y).2).getD j false)]⟩ :
          View).encode
        (List.ofFn ((yaoFunctionality Y).f n x y).1) := by
  rw [FakeSimulator.idealB_eq]
  dsimp only [data]
  rw [FakeSimulator.Data.make_answersAt, FakeSimulator.Data.make_messageAt]

/-- One uniform SB and tape equivalence are fixed before the distinguisher or inputs. -/
theorem exists_fixedSB (Y : YaoCircuit) (E₁ E₂ : List Bool → List Bool)
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    ∃ SB : NUPPT, SB.Uniform ∧ SB.coins = yaoCoins Y ∧ ∀ n,
      ∃ e : (Fin (10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n) → Bool) ≃ SB.Coins n,
        (∀ r, List.ofFn (e r) = List.ofFn r) ∧
        ∀ (x : Fin ((yaoFunctionality Y).inA.eval n) → Bool)
          (y : Fin ((yaoFunctionality Y).inB.eval n) → Bool) r,
        (yaoFunctionality Y).idealB SB n x y (e r) =
          pairEncode
            (⟨List.replicate n true, pairEncode (List.ofFn y)
              (List.ofFn (FakeObjects.activeAnswers (Y.circ n) (yaoSeed Y n (List.ofFn r))
                (Y.inA.eval n) (Y.inB.eval n))), [],
              [FakeObjects.message (nestedSpecial E₁ E₂ n) (Y.circ n)
                (yaoSeed Y n (List.ofFn r)) (Y.inA.eval n) (Y.outLen.eval n) (Y.outs n)
                (fun j => (List.ofFn ((yaoFunctionality Y).f n x y).2).getD j false)]⟩ :
              View).encode
            (List.ofFn ((yaoFunctionality Y).f n x y).1) := by
  obtain ⟨gen, hgen, hgenEq⟩ := Y.uniform
  let d := data Y E₁ E₂ hE₁ hE₂ gen hgen hgenEq
  let SB := FakeSimulator.simulator d (yaoCoins Y)
  have hLen n : SB.coinLen n = 10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n := by
    rw [NUPPT.coinLen_eq, FakeSimulator.simulator_coins, yaoCoins_eval]
  let e n : (Fin (10 * Y.sizeBound.eval n * n + 2 * Y.sizeBound.eval n) → Bool) ≃
      SB.Coins n := Equiv.arrowCongr (finCongr (hLen n).symm) (Equiv.refl Bool)
  have he n r : List.ofFn (e n r) = List.ofFn r :=
    ofFn_arrowCongr_finCongr (hLen n).symm r
  refine ⟨SB, FakeSimulator.simulator_uniform d _, FakeSimulator.simulator_coins d _, ?_⟩
  intro n
  refine ⟨e n, he n, ?_⟩
  intro x y r
  have h := ideal_eq Y E₁ E₂ hE₁ hE₂ gen hgen hgenEq n x y (e n r)
  simpa only [he n r] using h

end TCSlib.Cryptography.SecureComputation.YaoSpecializationProbe
