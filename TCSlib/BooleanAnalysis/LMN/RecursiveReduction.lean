import TCSlib.BooleanAnalysis.LMN.CircuitCompression
import TCSlib.BooleanAnalysis.LMN.CircuitHelpers
import TCSlib.BooleanAnalysis.LMN.RestrictionCompose
import Mathlib

/-!
# Recursive Circuit Reduction

Helper lemmas for the recursive proof of circuit_reduction_aux.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ## Restriction composition -/

private lemma restrictFn_composeRestr (f : (Fin n → Bool) → Bool) (ρ₁ ρ₂ : Restriction n) :
    restrictFn f (composeRestr ρ₁ ρ₂) = restrictFn (restrictFn f ρ₁) ρ₂ := by
  unfold restrictFn composeRestr Restriction.extend; aesop

/-! ## Circuit structure lemmas -/

lemma children_depth_le (isAnd : Bool) (cs : List (Circuit n)) (c : Circuit n) (hc : c ∈ cs)
    {d : ℕ} (hd : (Circuit.node isAnd cs).depth ≤ d) :
    c.depth ≤ d - 1 := by
  contrapose! hd;
  rw [ Circuit.depth ];
  have h_foldr : ∀ {l : List (Circuit n)}, c ∈ l → List.foldr (fun c acc => max c.depth acc) 0 l ≥ c.depth := by
    intros l hl; induction l <;> aesop;
  grind

lemma children_size_sum_le (isAnd : Bool) (cs : List (Circuit n))
    {s : ℕ} (hs : (Circuit.node isAnd cs).size ≤ s) :
    cs.foldr (fun c acc => c.size + acc) 0 ≤ s - 1 := by
  exact Nat.le_sub_one_of_lt ( lt_of_lt_of_le ( by cases cs <;> simp +decide [ Circuit.size ] ) hs )

lemma children_maxFanin_le (isAnd : Bool) (cs : List (Circuit n)) (c : Circuit n) (hc : c ∈ cs)
    {w : ℕ} (hw : (Circuit.node isAnd cs).maxFanin ≤ w) :
    c.maxFanin ≤ w := by
  have h_node : (Circuit.node isAnd cs).maxFanin = max cs.length (List.foldr (fun c acc => max c.maxFanin acc) 0 cs) := by
    simp [Circuit.maxFanin]
  rw [h_node] at hw
  have h_foldr : ∀ {l : List (Circuit n)}, c ∈ l → c.maxFanin ≤ List.foldr (fun c acc => max c.maxFanin acc) 0 l := by
    intros l hl; induction l <;> aesop;
  exact le_trans (h_foldr hc) (le_trans (le_max_right _ _) hw)

lemma child_size_le_parent (isAnd : Bool) (cs : List (Circuit n)) (c : Circuit n) (hc : c ∈ cs)
    {s : ℕ} (hs : (Circuit.node isAnd cs).size ≤ s) :
    c.size ≤ s - 1 := by
  -- Since $c$ is in $cs$, its size is included in the sum of the sizes of the children.
  have h_c_in_cs : c.size ≤ cs.foldr (fun c acc => c.size + acc) 0 := by
    induction cs <;> simp_all +arith +decide;
    cases hc <;> simp_all +arith +decide [ Circuit.size ];
    grind;
  exact h_c_in_cs.trans ( children_size_sum_le isAnd cs hs )

/-! ## Restriction and circuit evaluation -/

lemma restrictFn_node_eval (isAnd : Bool) (cs : List (Circuit n)) (ρ : Restriction n) :
    restrictFn (Circuit.eval (Circuit.node isAnd cs)) ρ =
    fun x => if isAnd
      then cs.foldr (fun c acc => restrictFn c.eval ρ x && acc) true
      else cs.foldr (fun c acc => restrictFn c.eval ρ x || acc) false := by
  unfold restrictFn;
  cases isAnd <;> simp +decide [ Circuit.eval ]

/-! ## Compression + switching -/

/-
When all children have dtDepth ≤ l, the AND node has a width-l CNF.
-/
lemma and_children_have_cnf (cs : List (Circuit n)) (ρ : Restriction n) (l : ℕ)
    (h_all : ∀ c ∈ cs, dtDepth (restrictFn c.eval ρ) ≤ l) :
    ∃ ψ : CNF n, CNF.width ψ ≤ l ∧
      ∀ x, CNF.eval ψ x = restrictFn (Circuit.eval (Circuit.node true cs)) ρ x := by
  -- Apply the compression_and_of_cnfs lemma to the list of functions obtained by restricting each child circuit to ρ.
  have h_compression : ∃ ψ : CNF n, CNF.width ψ ≤ l ∧ ∀ x, CNF.eval ψ x = (cs.map (fun c => restrictFn c.eval ρ)).all (fun f => f x) := by
    convert compression_and_of_cnfs _ _ _;
    exact fun f hf => by obtain ⟨ c, hc, rfl ⟩ := List.mem_map.mp hf; exact restricted_has_small_cnf_of_dtDepth_le _ _ _ ( h_all _ hc ) ;
  obtain ⟨ ψ, hψ₁, hψ₂ ⟩ := h_compression; use ψ; refine ⟨ hψ₁, fun x => ?_ ⟩ ; simp +decide [ *, restrictFn_node_eval ] ;
  clear h_all hψ₁ hψ₂;
  induction cs <;> aesop

/-
When all children have dtDepth ≤ l, the OR node has a width-l DNF.
-/
lemma or_children_have_dnf (cs : List (Circuit n)) (ρ : Restriction n) (l : ℕ)
    (h_all : ∀ c ∈ cs, dtDepth (restrictFn c.eval ρ) ≤ l) :
    ∃ φ : DNF n, DNF.width φ ≤ l ∧
      ∀ x, DNF.eval φ x = restrictFn (Circuit.eval (Circuit.node false cs)) ρ x := by
  convert compression_or_of_dnfs ( cs.map ( fun c => restrictFn c.eval ρ ) ) l _;
  · rename_i x;
    convert congr_fun ( restrictFn_node_eval false cs ρ ) x using 1;
    induction cs <;> aesop;
  · simp +zetaDelta at *;
    exact fun c hc => dtDepth_le_implies_small_dnf_cnf _ _ ( h_all c hc ) |>.1

/-
Combined: when all children have dtDepth ≤ l, further 1/(40l) restriction
    gives dtDepth ≤ t with high probability.
-/
lemma compress_and_switch (isAnd : Bool) (cs : List (Circuit n))
    (ρ₁ : Restriction n) (l t : ℕ) (hl : 0 < l) (hn : 0 < n)
    (h_all : ∀ c ∈ cs, dtDepth (restrictFn c.eval ρ₁) ≤ l) :
    bernoulliRestrProb (1 / (40 * (↑l : ℝ)))
      (fun ρ₂ => dtDepth (restrictFn (Circuit.eval (Circuit.node isAnd cs)) (composeRestr ρ₁ ρ₂)) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n / (120 * ↑l))) := by
  by_cases h : isAnd <;> simp_all +decide [ SwitchingLemma2.bernoulliRestrProb ];
  · have := and_children_have_cnf cs ρ₁ l h_all;
    obtain ⟨ψ, hψ_width, hψ_eval⟩ := this;
    convert switching_bernoulli_dtDepth_cnf_general ψ l hψ_width hl hn ( 1 / ( 40 * l ) ) ( by positivity ) ( by rw [ div_le_div_iff₀ ] <;> norm_cast <;> linarith ) ( by rw [ div_le_iff₀ ] <;> norm_cast <;> linarith ) t using 1;
    · simp +decide [ bernoulliRestrProb, hψ_eval ];
      exact congr_arg _ ( funext fun x => by rw [ restrictFn_composeRestr, show ψ.eval = _ from funext hψ_eval ] );
    · ring;
      norm_num [ add_comm ];
  · obtain ⟨ φ, hφ₁, hφ₂ ⟩ := or_children_have_dnf cs ρ₁ l h_all;
    -- Apply the switching lemma to the DNF φ.
    have h_switch : bernoulliRestrProb (1 / (40 * l)) (fun ρ₂ => dtDepth (restrictFn φ.eval ρ₂) > t) ≤ (1 / 2 : ℝ) ^ t + Real.exp (-(n / (120 * l))) := by
      convert switching_bernoulli_dtDepth_dnf_general φ l hφ₁ hl hn ( 1 / ( 40 * l ) ) ( by positivity ) ( by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith ) ( by rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith ) t using 1 ; ring;
    simp_all +decide [ SwitchingLemma2.bernoulliRestrProb ];
    convert h_switch using 3 ; simp +decide [ ← hφ₂, restrictFn_composeRestr ];
    rw [ show φ.eval = _ from funext hφ₂ ]

end LMN
end