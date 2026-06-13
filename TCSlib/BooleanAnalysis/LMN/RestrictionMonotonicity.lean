import TCSlib.BooleanAnalysis.LMN.RestrictionCompose
import TCSlib.BooleanAnalysis.LMN.SwitchingBernoulli
import Mathlib

/-!
# Restriction Monotonicity for Decision-Tree Depth

Decision-tree depth can only decrease under further restriction. This gives
a key monotonicity: `Pr_{p·q}[dtDepth > t] ≤ Pr_p[dtDepth > t]`, which
simplifies the high-probability depth reduction argument.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- Restrict a decision tree by a partial assignment. -/
def dtRestrict : DecisionTree n → Restriction n → DecisionTree n
  | .leaf b, _ => .leaf b
  | .branch var lo hi, ρ =>
    match ρ var with
    | some false => dtRestrict lo ρ
    | some true => dtRestrict hi ρ
    | none => .branch var (dtRestrict lo ρ) (dtRestrict hi ρ)

/-- Depth of restricted tree ≤ depth of original. -/
theorem dtRestrict_depth_le (T : DecisionTree n) (ρ : Restriction n) :
    (dtRestrict T ρ).depth ≤ T.depth := by
  induction' T with var lo hi ihlo ihhi
  · rfl
  · cases h : ρ lo <;> simp_all +decide [dtRestrict]
    · exact Nat.add_le_add_left (max_le_max ihhi ‹_›) _
    · cases ‹Bool› <;> simp_all +decide [DecisionTree.depth]
      · exact le_trans ihhi (by omega)
      · exact le_trans ‹_› (by omega)

/-- Restricted tree evaluates correctly. -/
theorem dtRestrict_eval (T : DecisionTree n) (ρ : Restriction n) (x : Fin n → Bool) :
    (dtRestrict T ρ).eval x = T.eval (Restriction.extend ρ x) := by
  induction T with
  | leaf b => simp [dtRestrict, DecisionTree.eval]
  | branch var lo hi ih_lo ih_hi =>
    simp only [dtRestrict]
    split
    · rename_i hv; rw [ih_lo]; simp [DecisionTree.eval, Restriction.extend, hv]
    · rename_i hv; rw [ih_hi]; simp [DecisionTree.eval, Restriction.extend, hv]
    · rename_i hv; simp [DecisionTree.eval, Restriction.extend, hv, ih_lo, ih_hi]

/-- **dtDepth monotonicity**: Decision-tree depth can only decrease under restriction.
    `dtDepth(f|_ρ) ≤ dtDepth(f)` for any function f and restriction ρ. -/
theorem dtDepth_restrictFn_le' (f : (Fin n → Bool) → Bool) (ρ : Restriction n) :
    dtDepth (restrictFn f ρ) ≤ dtDepth f := by
  obtain ⟨T, hTd, hTe⟩ := Nat.find_spec
    (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x)
    ⟨n, buildFullDTree f 0 (fun _ => false),
     buildFullDTree_depth f 0 (Nat.zero_le n) _,
     fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
  set T' := dtRestrict T ρ
  have hT'd : T'.depth ≤ dtDepth f := le_trans (dtRestrict_depth_le T ρ) hTd
  have hT'e : ∀ x, T'.eval x = restrictFn f ρ x := by
    intro x; rw [show T' = dtRestrict T ρ from rfl, dtRestrict_eval]
    simp [restrictFn]; exact hTe _
  exact Nat.find_min' _ ⟨T', hT'd, hT'e⟩

/-- Composing restrictions can only further decrease dtDepth. -/
theorem dtDepth_composeRestr_le (f : (Fin n → Bool) → Bool)
    (ρ₁ ρ₂ : Restriction n) :
    dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) ≤ dtDepth (restrictFn f ρ₁) := by
  suffices h : restrictFn f (composeRestr ρ₁ ρ₂) = restrictFn (restrictFn f ρ₁) ρ₂ by
    rw [h]; exact dtDepth_restrictFn_le' _ ρ₂
  ext x; simp only [restrictFn]
  congr 1; ext i
  simp only [composeRestr, Restriction.extend]
  cases ρ₁ i <;> simp [Option.getD]

/-
**Bernoulli probability monotonicity**: Under a stronger restriction
    (product of parameters), the probability that `dtDepth(f|_ρ) > t`
    can only decrease.
-/
theorem bernoulliRestrProb_dtDepth_compose_le
    (f : (Fin n → Bool) → Bool) (t : ℕ)
    (p₁ p₂ : ℝ) (hp₁ : 0 < p₁) (hp₁₁ : p₁ ≤ 1) (hp₂ : 0 < p₂) (hp₂₁ : p₂ ≤ 1) :
    bernoulliRestrProb (p₁ * p₂) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
    bernoulliRestrProb p₁ (fun ρ => dtDepth (restrictFn f ρ) > t) := by
  rw [restriction_compose_eq p₁ p₂ hp₁ hp₁₁ hp₂ hp₂₁]
  apply Finset.sum_le_sum
  intro ρ₁ _
  by_cases h : dtDepth (restrictFn f ρ₁) > t
  · -- dtDepth > t: inner Pr ≤ 1
    calc bernoulliRestrWeight p₁ ρ₁ *
          bernoulliRestrProb p₂ (fun ρ₂ => dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) > t)
        ≤ bernoulliRestrWeight p₁ ρ₁ * 1 :=
          mul_le_mul_of_nonneg_left (bernoulliRestrProb_le_one' p₂ hp₂.le hp₂₁ _)
            (bernoulliRestrWeight_nonneg' p₁ hp₁.le hp₁₁ _)
      _ = bernoulliRestrWeight p₁ ρ₁ * (if dtDepth (restrictFn f ρ₁) > t then 1 else 0) := by
          simp [h]
  · -- dtDepth ≤ t: further restriction can only decrease dtDepth
    push_neg at h
    have h_zero : bernoulliRestrProb p₂
        (fun ρ₂ => dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) > t) = 0 := by
      simp only [bernoulliRestrProb]
      apply Finset.sum_eq_zero; intro ρ₂ _
      have : ¬(dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) > t) := by
        push_neg; exact le_trans (dtDepth_composeRestr_le f ρ₁ ρ₂) h
      simp [this]
    rw [h_zero, mul_zero]
    exact mul_nonneg (bernoulliRestrWeight_nonneg' p₁ hp₁.le hp₁₁ _)
      (by simp [show ¬(dtDepth (restrictFn f ρ₁) > t) from by omega])

end LMN
end