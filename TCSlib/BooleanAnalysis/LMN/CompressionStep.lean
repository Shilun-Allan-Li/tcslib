import TCSlib.BooleanAnalysis.LMN.CircuitLayerReduction
import Mathlib

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

/-- Base case of `layer2_composed_bound`: d_inner = 2.
    c_top has depth 0 (literal), so the function is a single DNF gate
    (or its negation). The switching lemma bounds dtDepth. -/
lemma layer2_composed_bound_base (data : Layer2Data n) (c_top : Circuit data.numGates)
    (s_rem l t : ℕ) (hl_pos : 0 < l) (hn : 0 < n)
    (hd_depth : c_top.depth + 2 ≤ 2)
    (hs : c_top.size ≤ s_rem) (hwl : data.width ≤ l) (hs_pos : 0 < s_rem) :
    bernoulliRestrProb (composedDelta l (↑l) 2)
      (fun ρ => dtDepth (restrictFn (fun x => c_top.eval (fun i => (data.gates i).eval x)) ρ) > t) ≤
    ↑s_rem * (1 / 2 : ℝ) ^ l + (1 / 2 : ℝ) ^ t +
    ↑s_rem * Real.exp (-(↑n / (120 * ↑l))) + Real.exp (-(↑n / (120 * ↑l))) := by
  obtain ⟨l', hl'⟩ : ∃ l' : BoolCircuit.Lit data.numGates, c_top = Circuit.lit l' := by
    exact circuit_depth_zero_is_lit c_top ( by linarith );
  -- Apply the switching lemma to the DNF gate.
  have h_switching : bernoulliRestrProb (1 / (40 * l : ℝ)) (fun ρ => dtDepth (restrictFn (fun x => (data.gates l'.idx).eval x) ρ) > t) ≤ (1 / 2 : ℝ) ^ t + Real.exp (-(n / (120 * l))) := by
    have := @switching_bernoulli_dtDepth_dnf_general n ( data.gates l'.idx ) l;
    convert this ( data.widthBound _ |> le_trans <| hwl ) hl_pos hn ( 1 / ( 40 * l : ℝ ) ) ( by positivity ) ( by norm_num ) ( by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ) t using 1 ; ring;
  by_cases h : l'.sign <;> simp_all +decide [ Circuit.eval ];
  · unfold composedDelta; norm_num; linarith [ show ( 0 : ℝ ) ≤ s_rem * ( 2 ^ l ) ⁻¹ by positivity, show ( 0 : ℝ ) ≤ s_rem * Real.exp ( - ( n / ( 120 * l ) ) ) by positivity ] ;
  · refine le_trans ?_ ( le_trans h_switching ?_ );
    · unfold composedDelta; norm_num;
      unfold restrictFn; norm_num [ dtDepth_neg ] ;
    · nlinarith [ show ( s_rem : ℝ ) ≥ 1 by norm_cast, show ( 2 ^ l : ℝ ) ⁻¹ ≥ 0 by positivity, show ( Real.exp ( - ( n / ( 120 * l ) ) ) : ℝ ) ≥ 0 by positivity ]

/-! ## Constructing new DNF gates from switched gates -/

/-- After switching (dtDepth ≤ l for each gate), we can extract nice width-l DNFs
    that represent the restricted gate functions. -/
lemma switched_gates_give_new_dnfs
    (m : ℕ) (gates : Fin m → DNF n) (ρ₁ : Restriction n) (l : ℕ)
    (h_switch : ∀ i : Fin m, dtDepth (restrictFn (gates i).eval ρ₁) ≤ l) :
    ∃ (gates' : Fin m → DNF n),
      (∀ i, (gates' i).width ≤ l) ∧
      (∀ i, ∀ x, (gates' i).eval x = restrictFn (gates i).eval ρ₁ x) ∧
      (∀ i, ∀ t ∈ gates' i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ i, ∀ t ∈ gates' i, t.Nodup) := by
  have h_each : ∀ i : Fin m, ∃ φ : DNF n, φ.width ≤ l ∧
      (∀ x, φ.eval x = restrictFn (gates i).eval ρ₁ x) ∧
      (∀ t ∈ φ, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) ∧
      (∀ t ∈ φ, t.Nodup) := by
    intro i
    obtain ⟨⟨φ₀, hw₀, heval₀⟩, _⟩ := dtDepth_le_implies_small_dnf_cnf _ l (h_switch i)
    exact ⟨cleanDNF φ₀,
      le_trans (cleanDNF_width_le φ₀) hw₀,
      fun x => by rw [cleanDNF_eval]; exact heval₀ x,
      cleanDNF_var_inj φ₀,
      cleanDNF_nodup φ₀⟩
  choose gates' hgates' using h_each
  exact ⟨gates',
    fun i => (hgates' i).1,
    fun i => (hgates' i).2.1,
    fun i => (hgates' i).2.2.1,
    fun i => (hgates' i).2.2.2⟩

end LMN
end
