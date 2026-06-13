import TCSlib.BooleanAnalysis.LMN.CircuitLayerReduction
import Mathlib

/-!
# Helper lemmas for the one-step layer reduction

This file provides helper lemmas decomposing the one-step layer reduction
argument (proof steps 7 and 8 of the LMN theorem).

## Proof Strategy

### Step 7: 1/(40w)-random restriction
Under a Bernoulli(1/(40w)) random restriction, the bottom-layer DNF gates
(width ≤ w) are switched to decision trees of depth ≤ l. By the union bound,
the probability that any gate fails is ≤ s₂ · ((1/2)^l + exp(-n·p/3)).
When switching succeeds, each gate can be expressed as a width-l CNF.
Compression (AND of CNFs → single CNF, or OR of DNFs → single DNF) reduces
the circuit depth, yielding a circuit with width-l formulas at the next layer.

### Step 8: 1/(40l)-random restriction
The compressed circuit now has width-l formulas at its bottom layer.
A Bernoulli(1/(40l)) random restriction switches these to depth-l decision
trees (hence width-l DNFs), except with probability ≤ s₃ · ((1/2)^l + exp(-n/(120l))).
Compression then reduces depth by another layer. This is repeated for each
remaining layer.

## Technical Note on the Chernoff Tail

The switching lemma with parameter p gives tail exp(-n·p/3). When the
composed restriction parameter is very small (p = composedDelta ≪ 1/(40l)),
this tail approaches 1, which is too large. The correct approach decomposes
the composed restriction into individual stages of p = 1/(40l), where each
stage has tail exp(-n/(120l)). This decomposition is handled by the
two-stage bound infrastructure.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ## The switching step for Layer2Data gates

This captures proof-step 8: Under a 1/(40l)-random restriction, all
width-l DNF gates become depth-l decision trees (hence can be expressed
as width-l DNFs/CNFs), except with probability bounded by the union bound.
-/

/-
The switching step for Layer2Data gates: under a Bernoulli(1/(40l))
    restriction, the probability that some gate has dtDepth > l is bounded
    by numGates · ((1/2)^l + exp(-n/(120l))). This is the union bound
    over all gates applied at ONE stage of the iteration.
-/
lemma layer2_one_step_switching_bound
    (data : Layer2Data n) (l : ℕ) (hl_pos : 0 < l) (hn : 0 < n)
    (hwl : data.width ≤ l) :
    bernoulliRestrProb (1 / (40 * (↑l : ℝ)))
      (fun ρ => ∃ i : Fin data.numGates,
        dtDepth (restrictFn (data.gates i).eval ρ) > l) ≤
    ↑data.numGates * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n / (120 * ↑l)))) := by
  convert normalform_one_step_switching data l hn ( 1 / ( 40 * l ) ) _ _ _ using 1 <;> norm_num [ hl_pos ] ; ring_nf;
  · norm_num;
  · exact inv_anti₀ ( Nat.cast_pos.mpr data.widthPos ) ( Nat.cast_le.mpr hwl );
  · exact le_trans ( mul_le_mul_of_nonneg_right ( inv_le_one_of_one_le₀ ( mod_cast hl_pos ) ) ( by norm_num ) ) ( by norm_num )

/-
After successful switching (¬A), each gate can be replaced by a
    width-l CNF. This is the replaceability condition needed for
    compression (AND of CNFs → single CNF).
-/
lemma layer2_gates_switchable_to_cnf
    (data : Layer2Data n) (l : ℕ) (hl_pos : 0 < l) (hn : 0 < n)
    (hwl : data.width ≤ l) :
    bernoulliRestrProb (1 / (40 * (↑l : ℝ)))
      (fun ρ => ¬ ∀ i : Fin data.numGates,
        ∃ ψ : CNF n, CNF.width ψ ≤ l ∧
          ∀ x, CNF.eval ψ x = restrictFn (data.gates i).eval ρ x) ≤
    ↑data.numGates * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n / (120 * ↑l)))) := by
  convert normalform_one_step_cnf_replaceability data l hn ( 1 / ( 40 * l : ℝ ) ) ( by positivity ) _ _ using 2;
  · ring;
  · gcongr;
    exact mul_pos ( by norm_num ) ( Nat.cast_pos.mpr data.widthPos );
  · exact div_le_self zero_le_one ( by norm_cast; linarith )

end LMN
end