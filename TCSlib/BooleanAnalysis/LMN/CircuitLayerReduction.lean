import TCSlib.BooleanAnalysis.LMN.IterativeReduction
import TCSlib.BooleanAnalysis.LMN.CircuitCompression
import TCSlib.BooleanAnalysis.LMN.RestrictionCompose
import TCSlib.BooleanAnalysis.LMN.NormalFormConversion
import TCSlib.BooleanAnalysis.LMN.CircuitHelpers
import TCSlib.BooleanAnalysis.LMN.RestrictionMonotonicity
import TCSlib.BooleanAnalysis.LMN.RecursiveReduction
import Mathlib

/-!
# Iterative Circuit Layer Reduction

This file proves the core iterative reduction theorem of the LMN argument:
under a composed Bernoulli random restriction, the decision-tree depth of a
function computed by a bounded-depth circuit is small with high probability.

## Proof Structure (following LMN / O'Donnell Lemma 4.28)

The proof proceeds by strong induction on the circuit depth `d`:

**Base case (d = 2)**: The circuit is a depth-2 formula (DNF or CNF of width ≤ w).
Apply the switching lemma directly under a Bernoulli(1/(40w)) restriction.

**Inductive step (d ≥ 3)**: Factor `composedDelta w l d = composedDelta w l (d-1) · (1/(40l))`.
Use a two-stage argument:
- **Stage 1** (composedDelta w l (d-1)): Apply the IH to each child of the root gate.
  Each child has depth ≤ d-1, so by IH its dtDepth drops to ≤ l with high probability.
  By a union bound over at most s children, the failure probability is ≤ (s-1)·(½)^l + tail.
- **Stage 2** (1/(40l)): When all children have dtDepth ≤ l, each has a width-l
  CNF and DNF. Compress:
  - AND node + CNFs → single CNF of width l  (Steps 4–6)
  - OR node + DNFs → single DNF of width l   (Steps 4–6)
  Apply the switching lemma to the compressed formula → dtDepth ≤ t w.h.p.

The key property making the union bound tight: when the IH bound for child cᵢ
of size sᵢ is `(sᵢ - 1)·(½)^l + (½)^l + ...`, the `(sᵢ - 1)` and `(½)^l`
terms telescope: `Σᵢ (sᵢ - 1 + 1) = Σᵢ sᵢ = s - 1`.

## Main results

- `composedDelta`: the composed restriction parameter `δ = (1/(40w))·(1/(40l))^{d-2}`
- `circuit_reduction_aux`: the core bound by induction on d
- `circuit_reduction_core`: user-friendly reformulation
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ## Composed Restriction Parameters -/

def composedDelta (w : ℕ) (l : ℝ) (d : ℕ) : ℝ :=
  (1 / (40 * ↑w)) * (1 / (40 * l)) ^ (d - 2)

lemma composedDelta_pos (w : ℕ) (l : ℝ) (d : ℕ) (hw : 0 < w) (hl : 0 < l) :
    0 < composedDelta w l d := by unfold composedDelta; positivity

lemma composedDelta_le_one (w : ℕ) (l : ℝ) (d : ℕ) (hw : 1 ≤ w) (hl : 1 ≤ l) (hd : 2 ≤ d) :
    composedDelta w l d ≤ 1 := by
  exact mul_le_one₀ (by rw [div_le_iff₀] <;> norm_cast <;> linarith) (by positivity)
    (pow_le_one₀ (by positivity) (by rw [div_le_iff₀] <;> linarith))

lemma composedDelta_step (w l : ℕ) (d : ℕ) (hd : 3 ≤ d) :
    composedDelta w (↑l : ℝ) d = (1 / (40 * (↑w : ℝ))) * composedDelta l (↑l : ℝ) (d - 1) := by
  rcases d with ( _ | _ | d ) <;> norm_num [ composedDelta ] at *;
  cases d <;> simp_all +decide [ pow_succ' ]

/-- Factor composedDelta as the (d-1) case times 1/(40l). -/
lemma composedDelta_step_right (w : ℕ) (l : ℝ) (d : ℕ) (hd : 3 ≤ d) (hl : 0 < l) :
    composedDelta w l d = composedDelta w l (d - 1) * (1 / (40 * l)) := by
  rcases d with ( _ | _ | d ) <;> norm_num [ composedDelta ] at *
  cases d <;> simp_all +decide [ pow_succ' ] <;> ring

/-! ## Infrastructure -/

-- Layer2Data and related infrastructure kept for potential future use
structure Layer2Data (n : ℕ) where
  numGates : ℕ
  gates : Fin numGates → DNF n
  width : ℕ
  widthBound : ∀ i, (gates i).width ≤ width
  widthPos : 0 < width
  varInj : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂
  nodup : ∀ i, ∀ t ∈ gates i, t.Nodup

theorem normalform_one_step_switching (data : Layer2Data n) (l : ℕ) (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑data.width)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p (fun ρ => ∃ i : Fin data.numGates,
        dtDepth (restrictFn (data.gates i).eval ρ) > l) ≤
    ↑data.numGates * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) :=
  switching_bernoulli_union_bound data.gates data.width l
    data.widthBound data.widthPos data.varInj data.nodup hn p hp_pos hp_le hp1

theorem normalform_one_step_cnf_replaceability (data : Layer2Data n) (l : ℕ) (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑data.width)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p (fun ρ => ¬ ∀ i : Fin data.numGates,
        ∃ ψ : CNF n, CNF.width ψ ≤ l ∧ ∀ x, CNF.eval ψ x = restrictFn (data.gates i).eval ρ x) ≤
    ↑data.numGates * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) :=
  one_step_reduction_failure_bound data.gates data.width l
    data.widthBound data.widthPos data.varInj data.nodup hn p hp_pos hp_le hp1

theorem full_iterative_bound (m : ℕ) (layerSize : Fin m → ℕ) (s : ℕ)
    (h_sum : ∑ i, layerSize i ≤ s) (α β : ℝ) (hα : 0 ≤ α)
    (per_layer : Fin m → ℝ) (h_per : ∀ i, per_layer i ≤ ↑(layerSize i) * α)
    (final : ℝ) (h_final : final ≤ β) :
    (∑ i, per_layer i) + final ≤ ↑s * α + β :=
  add_le_add (multi_stage_failure_bound m layerSize s h_sum α hα per_layer h_per) h_final

/-! ## Restriction Composition and Two-Stage Bound -/

lemma restrictFn_composeRestr' (f : (Fin n → Bool) → Bool) (ρ₁ ρ₂ : Restriction n) :
    restrictFn f (composeRestr ρ₁ ρ₂) = restrictFn (restrictFn f ρ₁) ρ₂ := by
  unfold restrictFn composeRestr Restriction.extend; aesop

theorem two_stage_bound'
    (p₁ p₂ : ℝ) (hp₁ : 0 < p₁) (hp₁_1 : p₁ ≤ 1) (hp₂ : 0 < p₂) (hp₂_1 : p₂ ≤ 1)
    (E : Restriction n → Prop) [DecidablePred E]
    (A : Restriction n → Prop) [DecidablePred A]
    (β : ℝ) (hβ : 0 ≤ β)
    (h_bound : ∀ ρ₁, ¬A ρ₁ →
      bernoulliRestrProb p₂ (fun ρ₂ => E (composeRestr ρ₁ ρ₂)) ≤ β) :
    bernoulliRestrProb (p₁ * p₂) E ≤ bernoulliRestrProb p₁ A + β := by
  rw [ restriction_compose_eq, add_comm ];
  · rw [ add_comm ];
    have h_sum_bound : ∑ ρ₁, bernoulliRestrWeight p₁ ρ₁ * bernoulliRestrProb p₂ (fun ρ₂ => E (composeRestr ρ₁ ρ₂)) ≤ ∑ ρ₁, bernoulliRestrWeight p₁ ρ₁ * (if A ρ₁ then 1 else β) := by
      gcongr;
      · exact bernoulliRestrWeight_nonneg' p₁ hp₁.le hp₁_1 _;
      · split_ifs <;> [ exact bernoulliRestrProb_le_one' p₂ hp₂.le hp₂_1 _; exact h_bound _ ‹_› ];
    refine le_trans h_sum_bound ?_;
    simp +decide [ bernoulliRestrProb, Finset.sum_ite ];
    rw [ ← Finset.sum_mul _ _ _ ];
    exact mul_le_of_le_one_left hβ ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => bernoulliRestrWeight_nonneg' _ hp₁.le hp₁_1 _ ) ( by simp +decide [ bernoulliRestrWeight_sum_one _ hp₁.le hp₁_1 ] ) );
  · grind;
  · linarith;
  · exact?;
  · linarith

/-! ## Base Case: Depth-2 Circuits -/

lemma bernoulliRestrProb_dtDepth_mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (Fin n → Bool) → Bool) (l₁ l₂ : ℕ) (h : l₁ ≤ l₂) :
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > l₂) ≤
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > l₁) :=
  bernoulliRestrProb_mono p hp hp1 _ _ (fun _ hgt => by omega)

lemma bernoulliRestrProb_congr_fn' {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) :
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > t) =
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn g ρ) > t) := by
  have : f = g := funext h
  subst this; rfl

/-- Base case: depth-2 circuit → switching lemma bound. -/
lemma depth2_circuit_switching_bound
    (f : (Fin n → Bool) → Bool) (s w : ℕ) (hw_pos : 0 < w) (hn : 0 < n)
    (hc : ∃ c : Circuit n, c.depth ≤ 2 ∧ c.size ≤ s ∧ Circuit.maxFanin c ≤ w ∧
      ∀ x, c.eval x = f x)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) (t : ℕ) :
    bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p / 3)) := by
  obtain ⟨c, hcd, _, hcf, hce⟩ := hc
  rw [bernoulliRestrProb_congr_fn' (fun x => (hce x).symm)]
  cases c with
  | lit l =>
    let lit_dnf : DNF n := [[l.toLiteral]]
    have h_eval : ∀ x, lit_dnf.eval x = Lit.eval l x := by
      intro x; simp [lit_dnf, DNF.eval, Term.eval, Literal.eval, Lit.eval, Lit.toLiteral]
      cases l.sign <;> simp
    have h_circ_eval : (Circuit.lit l).eval = Lit.eval l := by ext x; simp [Circuit.eval]
    have h_rw : (Circuit.lit l).eval = lit_dnf.eval := by rw [h_circ_eval]; exact funext (fun x => (h_eval x).symm)
    rw [h_rw]
    apply switching_bernoulli_dtDepth_dnf_general lit_dnf w
    · simp [lit_dnf, DNF.width, Term.width]; omega
    · exact hw_pos
    · exact hn
    · exact hp_pos
    · exact hp_le
    · exact hp1
  | node isAnd cs =>
    cases isAnd with
    | false =>
      have h_eval : ∀ x, (depth2OrToDNF cs).eval x = Circuit.eval (Circuit.node false cs) x :=
        depth2OrToDNF_eval cs hcd
      rw [show Circuit.eval (Circuit.node false cs) = (depth2OrToDNF cs).eval
          from funext (fun x => (h_eval x).symm)]
      exact switching_bernoulli_dtDepth_dnf_general (depth2OrToDNF cs) w
        (le_trans (depth2OrToDNF_width_le cs hcd) hcf)
        hw_pos hn p hp_pos hp_le hp1 t
    | true =>
      have h_eval : ∀ x, CNF.eval (depth2AndToCNF cs) x = Circuit.eval (Circuit.node true cs) x :=
        depth2AndToCNF_eval cs hcd
      rw [show Circuit.eval (Circuit.node true cs) = CNF.eval (depth2AndToCNF cs)
          from funext (fun x => (h_eval x).symm)]
      exact switching_bernoulli_dtDepth_cnf_general (depth2AndToCNF cs) w
        (le_trans (depth2AndToCNF_width_le cs hcd) hcf)
        hw_pos hn p hp_pos hp_le hp1 t

/-! ## The Iterative Reduction: Inductive Proof

By strong induction on d. Base case d=2 uses the switching lemma directly.
Inductive step d≥3 uses a **two-stage argument**:
  1. Factor composedDelta(w, l, d) = composedDelta(w, l, d-1) · (1/(40l))
  2. Stage 1 (IH): Under composedDelta(w, l, d-1), each child has dtDepth ≤ l
     with high probability (by IH applied to each child, then union bound).
  3. Stage 2: When all children have dtDepth ≤ l, compress to width-l
     CNF/DNF and apply switching lemma under 1/(40l).

The bound:
  ≤ (s-1)·(½)^l + (½)^t + (s-1)·exp(-n/(120w)) + s·exp(-n/(120l))
  ≤ s·(½)^l + (½)^t + s·exp(-n/(120w)) + s·exp(-n/(120l))
-/

/-
Base case: d = 2 satisfies the inductive bound.
-/
lemma circuit_reduction_ind_base
    (f : (Fin n → Bool) → Bool) (s w : ℕ) (l t : ℕ)
    (hs_pos : 0 < s) (hw_pos : 0 < w) (hl_pos : 0 < l)
    (hn : 0 < n)
    (h_circuit : ∃ c : Circuit n,
      c.depth ≤ 2 ∧ c.size ≤ s ∧ Circuit.maxFanin c ≤ w ∧ ∀ x, c.eval x = f x) :
    bernoulliRestrProb (composedDelta w (↑l) 2) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    (↑s - 1) * (1 / 2 : ℝ) ^ l + (1 / 2 : ℝ) ^ t +
    (↑s - 1) * Real.exp (-(↑n / (120 * ↑w))) +
    ↑s * Real.exp (-(↑n / (120 * ↑l))) := by
  obtain ⟨c, hc⟩ := h_circuit;
  by_cases hs : s = 1;
  · rcases c with ( _ | _ | _ | c ) <;> norm_num at *;
    · -- Since the circuit is a literal, its depth is 0.
      have h_depth_zero : ∀ ρ : Restriction n, dtDepth (restrictFn f ρ) ≤ 1 := by
        intro ρ
        have h_depth_zero : dtDepth (restrictFn f ρ) ≤ dtDepth f := by
          apply dtDepth_restrictFn_le';
        refine le_trans h_depth_zero ?_;
        rw [ show f = _ from funext fun x => Eq.symm ( hc.2.2.2 x ) ];
        unfold dtDepth;
        simp +decide [ Nat.find_le_iff ];
        use 1;
        simp +decide [ Circuit.eval ];
        use DecisionTree.branch (‹Lit n›.idx) (DecisionTree.leaf (if ‹Lit n›.sign then false else true)) (DecisionTree.leaf (if ‹Lit n›.sign then true else false));
        split_ifs <;> simp +decide [ *, DecisionTree.eval ]; all_goals exact Nat.le_add_left _ _;
      rcases t with ( _ | t ) <;> norm_num at *;
      · refine' le_trans ( Finset.sum_le_sum fun ρ _ => _ ) _;
        use fun ρ => bernoulliRestrWeight ( composedDelta w l 2 ) ρ;
        · split_ifs <;> norm_num [ bernoulliRestrWeight ];
          exact mul_nonneg ( pow_nonneg ( by exact mul_nonneg ( by positivity ) ( by positivity ) ) _ ) ( pow_nonneg ( by exact div_nonneg ( sub_nonneg.2 <| by exact mul_le_one₀ ( by rw [ div_le_iff₀ <| by positivity ] ; norm_cast ; linarith ) ( by positivity ) <| by exact pow_le_one₀ ( by positivity ) <| by rw [ div_le_iff₀ <| by positivity ] ; norm_cast ; linarith ) zero_le_two ) _ );
        · rw [ bernoulliRestrWeight_sum_one ];
          · norm_num [ hs ];
            positivity;
          · exact mul_nonneg ( by positivity ) ( by positivity );
          · exact composedDelta_le_one _ _ _ hw_pos ( mod_cast hl_pos ) ( by norm_num );
      · rw [ bernoulliRestrProb ];
        rw [ Finset.sum_eq_zero ] <;> norm_num;
        · exact add_nonneg ( add_nonneg ( add_nonneg ( mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hs_pos ) ) ( pow_nonneg ( by norm_num ) _ ) ) ( pow_nonneg ( by norm_num ) _ ) ) ( mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hs_pos ) ) ( Real.exp_nonneg _ ) ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.exp_nonneg _ ) );
        · grind;
    · rcases k : ‹List ( Circuit n ) › with ( _ | ⟨ _, _ | k ⟩ ) <;> simp_all +decide [ Circuit.depth, Circuit.size, Circuit.maxFanin ];
      · -- Since the function is constant, its decision tree depth is 0.
        have h_const : ∀ x, f x = false := by
          exact fun x => hc x ▸ by simp +decide [ Circuit.eval ] ;
        unfold bernoulliRestrProb; norm_num [ h_const ] ;
        rw [ Finset.sum_eq_zero ] <;> norm_num;
        · positivity;
        · intro x hx; rw [ show f = _ from funext h_const ] at hx; simp_all +decide [ dtDepth ] ;
          specialize hx 0 bot_le ( DecisionTree.leaf false ) ; simp_all +decide [ restrictFn ];
          exact absurd ( hx rfl ) ( by simp +decide [ DecisionTree.eval ] );
      · cases h : ‹Circuit n› <;> simp_all +decide [ Circuit.depth, Circuit.size, Circuit.maxFanin ];
      · rename_i a b c;
        rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> simp_all +decide [ Circuit.depth, Circuit.size, Circuit.maxFanin ];
    · cases ‹List ( Circuit n ) › <;> simp_all +decide [ Circuit.depth, Circuit.size, Circuit.maxFanin ];
      · -- Since $f$ is a constant function, its decision tree depth is 0.
        have h_const : ∀ ρ : Restriction n, dtDepth (restrictFn f ρ) = 0 := by
          unfold restrictFn; simp +decide [ show f = _ from funext fun x => Eq.symm ( hc x ) ] ;
          unfold dtDepth; simp +decide [ Circuit.eval ] ;
          exact ⟨ DecisionTree.leaf true, rfl, fun _ => rfl ⟩;
        by_cases ht : t = 0 <;> simp_all +decide [ bernoulliRestrProb ]; all_goals positivity;
      · cases ‹Circuit n› <;> simp_all +decide [ Circuit.size ];
  · -- For s ≥ 2, use depth2_circuit_switching_bound and nlinarith to close.
    have h_bound : bernoulliRestrProb (1 / (40 * w : ℝ)) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤ (1 / 2 : ℝ) ^ t + Real.exp (-(n / (120 * w))) := by
      convert depth2_circuit_switching_bound f s w hw_pos hn ⟨ c, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2 ⟩ ( 1 / ( 40 * w : ℝ ) ) ( by positivity ) ( by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith ) ( by rw [ div_le_iff₀ ] <;> norm_cast <;> nlinarith ) t using 1 ; ring;
    refine le_trans ?_ ( h_bound.trans ?_ );
    · unfold composedDelta; norm_num;
    · nlinarith only [ show ( s : ℝ ) ≥ 2 by norm_cast; exact Nat.lt_of_le_of_ne hs_pos ( Ne.symm hs ), show ( 1 / 2 : ℝ ) ^ l ≥ 0 by positivity, show ( Real.exp ( - ( n / ( 120 * w ) ) ) ) ≥ 0 by positivity, show ( Real.exp ( - ( n / ( 120 * l ) ) ) ) ≥ 0 by positivity ]

/-
Union bound over a List: Pr[∃ c ∈ cs, bad c] ≤ Σ Pr[bad c].
-/
lemma bernoulliRestrProb_list_union_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (cs : List (Circuit n))
    (bad : Circuit n → Restriction n → Prop)
    [inst : ∀ c, DecidablePred (bad c)] :
    bernoulliRestrProb p (fun ρ => ∃ c ∈ cs, bad c ρ) ≤
    cs.foldr (fun c acc => bernoulliRestrProb p (bad c) + acc) 0 := by
  convert bernoulliRestrProb_union_bound_fin p hp hp1 cs.length ( fun i => fun ρ => bad ( cs[i] ) ρ ) using 1;
  · congr! 2;
    constructor;
    · rintro ⟨ c, hc₁, hc₂ ⟩ ; obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hc₁; use ⟨ i, by aesop ⟩ ; aesop;
    · exact fun ⟨ i, hi ⟩ => ⟨ _, List.getElem_mem _, hi ⟩;
  · induction cs <;> simp +decide [ *, Fin.sum_univ_succ ]

/-
Inductive step: for d ≥ 3, the bound follows from the IH on children.
-/
lemma circuit_reduction_ind_step
    (f : (Fin n → Bool) → Bool) (d s w : ℕ) (l t : ℕ)
    (hd3 : 3 ≤ d) (hs_pos : 0 < s) (hw_pos : 0 < w) (hl_pos : 0 < l)
    (hn : 0 < n)
    (h_circuit : ∃ c : Circuit n,
      c.depth ≤ d ∧ c.size ≤ s ∧ Circuit.maxFanin c ≤ w ∧ ∀ x, c.eval x = f x)
    (ih : ∀ (g : (Fin n → Bool) → Bool) (s' : ℕ),
      0 < s' →
      (∃ c : Circuit n, c.depth ≤ d - 1 ∧ c.size ≤ s' ∧ Circuit.maxFanin c ≤ w ∧ ∀ x, c.eval x = g x) →
      bernoulliRestrProb (composedDelta w (↑l) (d - 1)) (fun ρ => dtDepth (restrictFn g ρ) > l) ≤
      (↑s' - 1) * (1 / 2 : ℝ) ^ l + (1 / 2 : ℝ) ^ l +
      (↑s' - 1) * Real.exp (-(↑n / (120 * ↑w))) +
      ↑s' * Real.exp (-(↑n / (120 * ↑l)))) :
    bernoulliRestrProb (composedDelta w (↑l) d) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    (↑s - 1) * (1 / 2 : ℝ) ^ l + (1 / 2 : ℝ) ^ t +
    (↑s - 1) * Real.exp (-(↑n / (120 * ↑w))) +
    ↑s * Real.exp (-(↑n / (120 * ↑l))) := by
  obtain ⟨c, hc⟩ := h_circuit
  generalize_proofs at *; (
  by_cases hc_lit : ∃ a, c = Circuit.lit a;
  · obtain ⟨a, rfl⟩ := hc_lit
    have h_depth : ∀ ρ, dtDepth (restrictFn (Circuit.eval (Circuit.lit a)) ρ) ≤ 1 := by
      intro ρ
      have h_depth : dtDepth (restrictFn (Circuit.eval (Circuit.lit a)) ρ) ≤ dtDepth (Circuit.eval (Circuit.lit a)) := by
        apply dtDepth_restrictFn_le'
      generalize_proofs at *; (
      refine le_trans h_depth ?_;
      unfold dtDepth; simp +decide [ Circuit.eval ] ;
      use 1, by norm_num, .branch a.idx (.leaf false) (.leaf true) |> fun T => if a.sign then T else .branch a.idx (.leaf true) (.leaf false) ; simp +decide [ DecisionTree.eval ] ;
      split_ifs <;> simp +decide [ DecisionTree.depth, DecisionTree.eval ])
    generalize_proofs at *; (
    by_cases ht : t ≥ 1 <;> simp +decide [ ← hc.2.2.2, ht ] at h_depth ⊢
    generalize_proofs at *; (
    rw [ show f = Circuit.eval ( Circuit.lit a ) from funext fun x => hc.2.2.2 x ▸ rfl ] ; simp +decide [ show ∀ ρ : Restriction n, ¬ ( dtDepth ( restrictFn ( Circuit.eval ( Circuit.lit a ) ) ρ ) > t ) from fun ρ => not_lt_of_ge ( le_trans ( h_depth ρ ) ( by linarith ) ) ] ; ring_nf ; norm_num [ hs_pos, hw_pos, hl_pos, hn ] ;
    unfold bernoulliRestrProb; norm_num; ring_nf; norm_num [ hs_pos, hw_pos, hl_pos, hn ] ;
    nlinarith [ show ( s : ℝ ) ≥ 1 by norm_cast, show ( 1 / 2 : ℝ ) ^ l ≥ 0 by positivity, show ( 1 / 2 : ℝ ) ^ t ≥ 0 by positivity, show ( Real.exp ( - ( n * ( w : ℝ ) ⁻¹ * ( 1 / 120 ) ) ) ) ≥ 0 by positivity, show ( Real.exp ( - ( n * ( l : ℝ ) ⁻¹ * ( 1 / 120 ) ) ) ) ≥ 0 by positivity, show ( 1 / 2 : ℝ ) ^ l ≤ 1 by exact pow_le_one₀ ( by positivity ) ( by norm_num ), show ( 1 / 2 : ℝ ) ^ t ≤ 1 by exact pow_le_one₀ ( by positivity ) ( by norm_num ) ]);
    refine' le_trans ( bernoulliRestrProb_le_one' _ _ _ _ ) _ <;> norm_num [ show t = 0 by linarith ] at *;
    · exact le_of_lt ( composedDelta_pos _ _ _ hw_pos ( Nat.cast_pos.mpr hl_pos ) );
    · exact composedDelta_le_one _ _ _ ( by linarith ) ( by norm_cast ) ( by linarith );
    · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( le_add_of_nonneg_left <| mul_nonneg ( sub_nonneg.mpr <| Nat.one_le_cast.mpr hs_pos ) <| inv_nonneg.mpr <| pow_nonneg zero_le_two _ ) <| mul_nonneg ( sub_nonneg.mpr <| Nat.one_le_cast.mpr hs_pos ) <| Real.exp_nonneg _ ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| Real.exp_nonneg _;);
  · obtain ⟨isAnd, cs, hc⟩ : ∃ isAnd cs, c = Circuit.node isAnd cs := by
      cases c <;> tauto
    generalize_proofs at *; (
    -- Apply the two-stage bound with the composedDelta probability.
    have h_two_stage : bernoulliRestrProb (composedDelta w l d) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
      bernoulliRestrProb (composedDelta w l (d - 1)) (fun ρ => ∃ c₀ ∈ cs, dtDepth (restrictFn c₀.eval ρ) > l) +
      ((1 / 2 : ℝ) ^ t + Real.exp (-(n / (120 * l)))) := by
        convert two_stage_bound' ( composedDelta w l ( d - 1 ) ) ( 1 / ( 40 * l ) ) _ _ _ _ _ _ _ _ _ using 1 <;> norm_num [ composedDelta_step_right, hd3, hl_pos ];
        congr! 1
        generalize_proofs at *; (
        exact composedDelta_pos _ _ _ hw_pos ( Nat.cast_pos.mpr hl_pos ));
        · exact composedDelta_le_one _ _ _ ( by linarith ) ( by norm_cast ) ( Nat.le_sub_one_of_lt hd3 );
        · exact le_trans ( mul_le_mul_of_nonneg_right ( inv_le_one_of_one_le₀ ( mod_cast hl_pos ) ) ( by norm_num ) ) ( by norm_num );
        · positivity;
        · intro ρ₁ hρ₁
          have h_restrict : f = fun x => Circuit.eval (Circuit.node isAnd cs) x := by
            grind +ring
          generalize_proofs at *; (
          convert compress_and_switch isAnd cs ρ₁ l t hl_pos hn hρ₁ using 1 ; norm_num [ h_restrict ])
    generalize_proofs at *; (
    -- Apply the union bound to the list of children.
    have h_union_bound : bernoulliRestrProb (composedDelta w l (d - 1)) (fun ρ => ∃ c₀ ∈ cs, dtDepth (restrictFn c₀.eval ρ) > l) ≤
      cs.foldr (fun c acc => bernoulliRestrProb (composedDelta w l (d - 1)) (fun ρ => dtDepth (restrictFn c.eval ρ) > l) + acc) 0 := by
        convert bernoulliRestrProb_list_union_bound _ _ _ _ _ using 1
        generalize_proofs at *; (
        exact le_of_lt ( composedDelta_pos _ _ _ hw_pos ( Nat.cast_pos.mpr hl_pos ) ));
        exact composedDelta_le_one _ _ _ ( by linarith ) ( by norm_cast ) ( by omega )
    generalize_proofs at *; (
    -- Apply the induction hypothesis to each child in the list.
    have h_induction : ∀ c₀ ∈ cs, bernoulliRestrProb (composedDelta w l (d - 1)) (fun ρ => dtDepth (restrictFn c₀.eval ρ) > l) ≤
      (c₀.size : ℝ) * (1 / 2 : ℝ) ^ l + (c₀.size - 1) * Real.exp (-(n / (120 * w))) + c₀.size * Real.exp (-(n / (120 * l))) := by
        intros c₀ hc₀
        have h_circuit : ∃ c' : Circuit n, c'.depth ≤ d - 1 ∧ c'.size ≤ c₀.size ∧ c'.maxFanin ≤ w ∧ ∀ x, c'.eval x = c₀.eval x := by
          use c₀; simp_all +decide [ children_depth_le, child_size_le_parent, children_maxFanin_le ] ;
          exact ⟨ children_depth_le isAnd cs c₀ hc₀ ( by tauto ), children_maxFanin_le isAnd cs c₀ hc₀ ( by tauto ) ⟩
        generalize_proofs at *; (
        by_cases hc₀_pos : 0 < c₀.size <;> simp_all +decide [ Nat.AtLeastTwo ];
        · obtain ⟨ c', hc'₁, hc'₂, hc'₃, hc'₄ ⟩ := h_circuit; specialize ih c₀.eval c₀.size hc₀_pos c' hc'₁ hc'₂ hc'₃ hc'₄; ring_nf at *; linarith;
        · obtain ⟨ c', hc'₁, hc'₂, hc'₃, hc'₄ ⟩ := h_circuit; simp_all +decide [ Circuit.size ] ;
          cases c' <;> simp_all +decide [ Circuit.size ])
    generalize_proofs at *; (
    have h_sum_bound : cs.foldr (fun c acc => (c.size : ℝ) * (1 / 2 : ℝ) ^ l + (c.size - 1) * Real.exp (-(n / (120 * w))) + c.size * Real.exp (-(n / (120 * l))) + acc) 0 ≤ (s - 1 : ℝ) * (1 / 2 : ℝ) ^ l + (s - 1) * Real.exp (-(n / (120 * w))) + (s - 1) * Real.exp (-(n / (120 * l))) := by
      have h_sum_bound : cs.foldr (fun c acc => (c.size : ℝ) + acc) 0 ≤ s - 1 := by
        have := children_size_sum_le isAnd cs ( show ( Circuit.node isAnd cs ).size ≤ s from by aesop ) ; norm_cast at *;
        rw [ Int.subNatNat_of_le ] <;> norm_cast;
        convert Nat.cast_le.mpr this using 1
        generalize_proofs at *; (
        clear this h_two_stage h_union_bound h_induction ih hc_lit hc ‹c.depth ≤ d ∧ c.size ≤ s ∧ c.maxFanin ≤ w ∧ ∀ x, c.eval x = f x› ‹Nat.AtLeastTwo 2› ‹Nat.AtLeastTwo 120›; induction cs <;> simp +decide [ * ] ;);
        · infer_instance;
        · infer_instance;
        · infer_instance
      generalize_proofs at *; (
      refine' le_trans _ ( add_le_add_three ( mul_le_mul_of_nonneg_right h_sum_bound <| by positivity ) ( mul_le_mul_of_nonneg_right h_sum_bound <| by positivity ) ( mul_le_mul_of_nonneg_right h_sum_bound <| by positivity ) );
      have h_sum_bound : ∀ (cs : List (Circuit n)), List.foldr (fun c acc => (c.size : ℝ) * (1 / 2 : ℝ) ^ l + (c.size - 1) * Real.exp (-(n / (120 * w))) + c.size * Real.exp (-(n / (120 * l))) + acc) 0 cs ≤
        List.foldr (fun c acc => (c.size : ℝ) + acc) 0 cs * (1 / 2 : ℝ) ^ l + List.foldr (fun c acc => (c.size : ℝ) + acc) 0 cs * Real.exp (-(n / (120 * w))) + List.foldr (fun c acc => (c.size : ℝ) + acc) 0 cs * Real.exp (-(n / (120 * l))) := by
          intro cs; induction cs <;> norm_num at * ; nlinarith [ Real.exp_pos ( - ( n / ( 120 * w ) ) ), Real.exp_pos ( - ( n / ( 120 * l ) ) ) ] ;
      generalize_proofs at *; (
      exact h_sum_bound cs))
    generalize_proofs at *; (
    have h_final_bound : List.foldr (fun c acc => bernoulliRestrProb (composedDelta w l (d - 1)) (fun ρ => dtDepth (restrictFn c.eval ρ) > l) + acc) 0 cs ≤
      List.foldr (fun c acc => (c.size : ℝ) * (1 / 2 : ℝ) ^ l + (c.size - 1) * Real.exp (-(n / (120 * w))) + c.size * Real.exp (-(n / (120 * l))) + acc) 0 cs := by
        have h_final_bound : ∀ (cs : List (Circuit n)), (∀ c₀ ∈ cs, bernoulliRestrProb (composedDelta w l (d - 1)) (fun ρ => dtDepth (restrictFn c₀.eval ρ) > l) ≤ (c₀.size : ℝ) * (1 / 2 : ℝ) ^ l + (c₀.size - 1) * Real.exp (-(n / (120 * w))) + c₀.size * Real.exp (-(n / (120 * l)))) → List.foldr (fun c acc => bernoulliRestrProb (composedDelta w l (d - 1)) (fun ρ => dtDepth (restrictFn c.eval ρ) > l) + acc) 0 cs ≤ List.foldr (fun c acc => (c.size : ℝ) * (1 / 2 : ℝ) ^ l + (c.size - 1) * Real.exp (-(n / (120 * w))) + c.size * Real.exp (-(n / (120 * l))) + acc) 0 cs := by
          intro cs hcs; induction cs <;> simp +decide [ * ] ;
          rename_i k hk ihk; specialize ihk ( fun c₀ hc₀ => hcs c₀ ( List.mem_cons_of_mem _ hc₀ ) ) ; simp_all +decide [ List.foldr ] ;
          exact add_le_add hcs.1 ihk
        generalize_proofs at *; (
        exact h_final_bound cs h_induction)
    generalize_proofs at *; (
    linarith [ Real.exp_pos ( - ( n / ( 120 * l ) ) ) ])))))))

/-
Key inductive lemma with tight coefficients.
    The coefficient (s-1) for (1/2)^l and exp_w allows the recursion to close:
    when summing over children, Σ(sᵢ-1+1) = Σsᵢ = s-1 (the +1 from each child's
    (1/2)^t term with t=l cancels the -1).
-/
theorem circuit_reduction_ind
    (f : (Fin n → Bool) → Bool) (d s w : ℕ) (l t : ℕ)
    (hd2 : 2 ≤ d) (hs_pos : 0 < s) (hw_pos : 0 < w) (hl_pos : 0 < l)
    (hn : 0 < n)
    (h_circuit : ∃ c : Circuit n,
      c.depth ≤ d ∧ c.size ≤ s ∧ Circuit.maxFanin c ≤ w ∧ ∀ x, c.eval x = f x) :
    bernoulliRestrProb (composedDelta w (↑l) d) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    (↑s - 1) * (1 / 2 : ℝ) ^ l + (1 / 2 : ℝ) ^ t +
    (↑s - 1) * Real.exp (-(↑n / (120 * ↑w))) +
    ↑s * Real.exp (-(↑n / (120 * ↑l))) := by
  induction' hd2 with d hd ih generalizing s w l t f <;> simp_all +decide;
  · convert circuit_reduction_ind_base f s w l t hs_pos hw_pos hl_pos hn h_circuit using 1;
    norm_num [ ← inv_pow ];
  · convert circuit_reduction_ind_step f ( d + 1 ) s w l t ( by linarith ) hs_pos hw_pos hl_pos hn h_circuit _ using 1;
    · norm_num [ ← inv_pow ];
    · simp +zetaDelta at *;
      exact fun g s' hs' x hx₁ hx₂ hx₃ hx₄ => ih g s' w l l hs' hw_pos hl_pos x hx₁ hx₂ hx₃ hx₄

theorem circuit_reduction_aux
    (f : (Fin n → Bool) → Bool) (d s w : ℕ) (l t : ℕ)
    (hd2 : 2 ≤ d) (hs_pos : 0 < s) (hw_pos : 0 < w) (hl_pos : 0 < l)
    (hn : 0 < n)
    (h_circuit : ∃ c : Circuit n,
      c.depth ≤ d ∧ c.size ≤ s ∧ Circuit.maxFanin c ≤ w ∧ ∀ x, c.eval x = f x) :
    bernoulliRestrProb (composedDelta w (↑l) d) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    ↑s * (1 / 2 : ℝ) ^ l + (1 / 2 : ℝ) ^ t +
    ↑s * Real.exp (-(↑n / (120 * ↑w))) +
    ↑s * Real.exp (-(↑n / (120 * ↑l))) := by
  have h := circuit_reduction_ind f d s w l t hd2 hs_pos hw_pos hl_pos hn h_circuit
  have hs1 : (0 : ℝ) ≤ (↑s : ℝ) - 1 := by
    have : (1 : ℝ) ≤ ↑s := Nat.one_le_cast.mpr hs_pos; linarith
  have hsl : (↑s : ℝ) - 1 ≤ ↑s := by linarith
  nlinarith [pow_nonneg (show (0:ℝ) ≤ 1/2 by norm_num) l,
            Real.exp_pos (-(↑n / (120 * ↑w))),
            Real.exp_pos (-(↑n / (120 * ↑l)))]

/-! ## Main Theorem -/

theorem circuit_reduction_core
    (f : (Fin n → Bool) → Bool) (d s w : ℕ) (l t : ℕ)
    (hd2 : 2 ≤ d) (hs_pos : 0 < s) (hw_pos : 0 < w) (hl_pos : 0 < l) (hn : 0 < n)
    (h_circuit : ∃ c : Circuit n,
      c.depth ≤ d ∧ c.size ≤ s ∧ Circuit.maxFanin c ≤ w ∧ ∀ x, c.eval x = f x) :
    bernoulliRestrProb (composedDelta w (↑l) d) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    ↑s * (1 / 2 : ℝ) ^ l + (1 / 2 : ℝ) ^ t +
    ↑s * Real.exp (-(↑n / (120 * ↑w))) +
    ↑s * Real.exp (-(↑n / (120 * ↑l))) :=
  circuit_reduction_aux f d s w l t hd2 hs_pos hw_pos hl_pos hn h_circuit

end LMN
end