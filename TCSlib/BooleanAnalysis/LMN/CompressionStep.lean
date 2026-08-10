import TCSlib.BooleanAnalysis.LMN.CircuitLayerReduction

/-!
# Compression Step for Layer Reduction

Helper lemmas for proving `layer2_composed_bound` and `one_step_layer_reduction`.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ## Base case: c_top is a literal (depth 0) -/

/-- When c_top has depth 0, it must be a literal. -/
lemma circuit_depth_zero_is_lit (c : Circuit m) (h : c.depth = 0) :
    ∃ (l : BoolCircuit.Lit m), c = Circuit.lit l := by
  cases c with
  | lit l => exact ⟨l, rfl⟩
  | node isAnd cs => simp [Circuit.depth] at h

/-! ## Constructing new DNF gates from switched gates -/

end LMN
end
