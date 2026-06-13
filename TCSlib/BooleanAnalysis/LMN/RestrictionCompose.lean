import TCSlib.BooleanAnalysis.Switching.BernoulliRestriction
import Mathlib

/-!
# Composition of Random Restrictions

This file proves that random restrictions compose: a Bernoulli(p) restriction
followed by a Bernoulli(q) restriction is equivalent to a Bernoulli(p*q)
restriction.

## Main results

- `composeRestr`: compose two restrictions (ρ₁ takes priority)
- `restriction_compose_eq`: the composition equality for `bernoulliRestrProb`
- `restriction_compose_le`: inequality corollary
-/

open BoolCircuit SwitchingLemma2
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

/-! ## Definitions -/

/-- Compose two restrictions: `ρ₁` takes priority (if it fixes a variable,
    that value is used); otherwise `ρ₂` determines the outcome.
    This models applying `ρ₁` first, then `ρ₂` on the remaining free variables. -/
def composeRestr (ρ₁ ρ₂ : Restriction n) : Restriction n :=
  fun i => (ρ₁ i).orElse (fun _ => ρ₂ i)

/-- Per-variable weight in the Bernoulli restriction model:
    free variables (`none`) have weight `p`,
    fixed variables (`some _`) have weight `(1-p)/2`. -/
def varWeight (p : ℝ) : Option Bool → ℝ
  | none => p
  | some _ => (1 - p) / 2

/-! ## Helper lemmas -/

/-- `composeRestr` is pointwise: `composeRestr ρ₁ ρ₂ = σ` iff every coordinate matches. -/
lemma composeRestr_eq_iff (ρ₁ ρ₂ σ : Restriction n) :
    composeRestr ρ₁ ρ₂ = σ ↔ ∀ i, (ρ₁ i).orElse (fun _ => ρ₂ i) = σ i := by
  constructor
  · intro h i; exact congr_fun h i
  · intro h; funext i; exact h i

/-- Basic property: composing with the identity restriction (all free) gives back the original. -/
lemma composeRestr_id_right (ρ : Restriction n) :
    composeRestr ρ (fun _ => none) = ρ := by
  funext i; simp [composeRestr, Option.orElse]; cases ρ i <;> simp

/--
The Bernoulli restriction weight factors as a product of per-variable weights.
-/
lemma bernoulliRestrWeight_eq_prod (p : ℝ) (ρ : Restriction n) :
    bernoulliRestrWeight p ρ = ∏ i : Fin n, varWeight p (ρ i) := by
  have h_split : ∏ i, varWeight p (ρ i) = (∏ i ∈ ρ.freeVars, p) * (∏ i ∈ Finset.univ \ ρ.freeVars, (1 - p) / 2) := by
    rw [← Finset.prod_sdiff <| Finset.subset_univ <| ρ.freeVars]
    rw [mul_comm]
    refine' congrArg₂ _ (Finset.prod_congr rfl fun x hx => _) (Finset.prod_congr rfl fun x hx => _) <;> simp_all +decide [Restriction.freeVars]
    · rfl
    · cases h : ρ x <;> aesop
  simp_all +decide [Finset.card_sdiff, Finset.card_singleton]
  unfold bernoulliRestrWeight; ring
  rw [show (1 / 2 + p * (-1 / 2)) = (1 - p) / 2 by ring]; rw [div_pow]; ring!
  norm_num

/--
Per-variable composition identity: the marginal weight under the composed
    Bernoulli(p) × Bernoulli(q) distribution equals the Bernoulli(p*q) weight.

    Concretely, for each outcome `c : Option Bool`:
    `∑_{a,b} vw_p(a) * vw_q(b) * [orElse(a,b) = c] = vw_{pq}(c)`
-/
lemma varWeight_compose_sum (p q : ℝ) (c : Option Bool) :
    ∑ a : Option Bool, ∑ b : Option Bool,
      varWeight p a * varWeight q b *
        (if a.orElse (fun _ => b) = c then (1 : ℝ) else 0)
    = varWeight (p * q) c := by
  rcases c with (_ | b) <;> simp +decide [varWeight]
  cases b <;> norm_num <;> ring

/--
The fiber weight identity: summing `w_p(ρ₁) * w_q(ρ₂)` over all `(ρ₁, ρ₂)`
    that compose to `σ` gives `w_{pq}(σ)`.
-/
lemma compose_fiber_weight_eq (p q : ℝ) (σ : Restriction n) :
    ∑ ρ₁ : Restriction n, ∑ ρ₂ : Restriction n,
      bernoulliRestrWeight p ρ₁ * bernoulliRestrWeight q ρ₂ *
        (if composeRestr ρ₁ ρ₂ = σ then (1 : ℝ) else 0)
    = bernoulliRestrWeight (p * q) σ := by
  have h_double_sum : ∑ ρ₁, ∑ ρ₂, bernoulliRestrWeight p ρ₁ * bernoulliRestrWeight q ρ₂ * (if composeRestr ρ₁ ρ₂ = σ then (1 : ℝ) else 0) =
    ∑ g : Fin n → (Option Bool × Option Bool),
    (∏ i, (varWeight p (g i).1 * varWeight q (g i).2 * (if (g i).1.orElse (fun _ => (g i).2) = σ i then (1 : ℝ) else 0))) := by
      have h_double_sum : ∑ ρ₁ : Fin n → Option Bool, ∑ ρ₂ : Fin n → Option Bool, bernoulliRestrWeight p ρ₁ * bernoulliRestrWeight q ρ₂ * (if composeRestr ρ₁ ρ₂ = σ then (1 : ℝ) else 0) =
        ∑ ρ₁ : Fin n → Option Bool, ∑ ρ₂ : Fin n → Option Bool, (∏ i, (varWeight p (ρ₁ i) * varWeight q (ρ₂ i) * (if (ρ₁ i).orElse (fun _ => (ρ₂ i)) = σ i then (1 : ℝ) else 0))) := by
          refine' Finset.sum_congr rfl fun ρ₁ _ => Finset.sum_congr rfl fun ρ₂ _ => _
          simp +decide [bernoulliRestrWeight_eq_prod, Finset.prod_mul_distrib, Finset.prod_ite]
          split_ifs <;> simp_all +decide [Finset.ext_iff, funext_iff, composeRestr]
      rw [h_double_sum, ← Finset.sum_product']
      refine' Finset.sum_bij (fun x _ => fun i => (x.1 i, x.2 i)) _ _ _ _ <;> simp +decide
      simp +contextual [funext_iff, Prod.ext_iff]
  have h_per_variable : ∀ i : Fin n, ∑ g : Option Bool × Option Bool, varWeight p g.1 * varWeight q g.2 * (if g.1.orElse (fun _ => g.2) = σ i then (1 : ℝ) else 0) = varWeight (p * q) (σ i) := by
    intro i
    apply varWeight_compose_sum p q (σ i) |> Eq.trans (by exact?)
  convert Finset.prod_congr rfl fun i _ => h_per_variable i using 1
  any_goals exact Finset.univ
  · rw [h_double_sum, Finset.prod_sum]
    refine' Finset.sum_bij (fun g _ => fun i _ => g i) _ _ _ _ <;> simp +decide
    · simp +decide [funext_iff]
    · exact fun b => ⟨fun i => b i (Finset.mem_univ i), funext fun i => funext fun _ => rfl⟩
  · exact?

/-! ## Main composition theorem -/

/--
**Composition of Bernoulli random restrictions** (equality version).

A Bernoulli(`p`) restriction followed by a Bernoulli(`q`) restriction on the
remaining free variables has the same distribution as a single Bernoulli(`p*q`)
restriction.
-/
theorem restriction_compose_eq (p q : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    bernoulliRestrProb (p * q) event =
    ∑ ρ₁ : Restriction n, bernoulliRestrWeight p ρ₁ *
      bernoulliRestrProb q (fun ρ₂ => event (composeRestr ρ₁ ρ₂)) := by
  unfold bernoulliRestrProb
  have h_sum : ∀ ρ : Restriction n, bernoulliRestrWeight (p * q) ρ * (if event ρ then 1 else 0) = ∑ ρ₁ : Restriction n, ∑ ρ₂ : Restriction n, bernoulliRestrWeight p ρ₁ * bernoulliRestrWeight q ρ₂ * (if composeRestr ρ₁ ρ₂ = ρ then (if event ρ then 1 else 0) else 0) := by
    intro ρ
    have h_sum : bernoulliRestrWeight (p * q) ρ = ∑ ρ₁ : Restriction n, ∑ ρ₂ : Restriction n, bernoulliRestrWeight p ρ₁ * bernoulliRestrWeight q ρ₂ * (if composeRestr ρ₁ ρ₂ = ρ then 1 else 0) := by
      convert compose_fiber_weight_eq p q ρ |> Eq.symm using 1
    split_ifs <;> simp +decide [*, Finset.sum_ite]
  simp +decide only [h_sum, Finset.mul_sum _ _ _]
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  intro ρ₁ hρ₁; rw [Finset.sum_comm]; simp +decide

/--
**Composition inequality**: a Bernoulli(`p*q`) event probability is at most
    the Bernoulli(`p`) probability that any `ρ₂` makes the event hold.
-/
theorem restriction_compose_le (p q : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    bernoulliRestrProb (p * q) event ≤
    bernoulliRestrProb p
      (fun ρ₁ => ∃ ρ₂ : Restriction n, event (composeRestr ρ₁ ρ₂)) := by
  rw [restriction_compose_eq p q hp hp1 hq hq1 event]
  refine' le_trans (Finset.sum_le_sum fun ρ₁ _ => mul_le_mul_of_nonneg_left _ (bernoulliRestrWeight_nonneg' p hp.le hp1 ρ₁)) _
  any_goals exact fun ρ₁ => if ∃ ρ₂, event (composeRestr ρ₁ ρ₂) then 1 else 0
  · split_ifs <;> simp_all +decide [bernoulliRestrProb]
    convert bernoulliRestrProb_le_one' q hq.le hq1 (fun ρ₂ => event (composeRestr ρ₁ ρ₂)) using 1
    exact Finset.sum_congr rfl fun _ _ => by aesop
  · unfold bernoulliRestrProb; aesop

end LMN
end
