import TCSlib.BooleanAnalysis.LMN.SwitchingBernoulli
import Mathlib

/-!
# Gate Switching under Bernoulli Restrictions (Step 4 of LMN)

This file formalizes the application of Håstad's switching lemma to individual
gates after the initial Bernoulli restriction.

## Main result

After applying a Bernoulli(`p`) restriction with `p ≤ 1/(40w)` to a width-`w`
DNF gate `g`, with high probability the restricted function `g|_ρ` has
decision-tree depth at most `l`. By `dtDepth_le_implies_small_dnf_cnf`, this
means `g|_ρ` can be expressed as a CNF of width at most `l`.

Concretely:
- `switching_bernoulli_gate_to_cnf`: For a width-`w` DNF `g` under Bernoulli(`p`),
  `Pr[g|_ρ cannot be written as a width-≤-l CNF] ≤ (1/2)^l + exp(-np/3)`.
- `switching_bernoulli_gate_to_dnf_from_cnf`: The dual for CNF gates.

These are the key bridge lemmas that connect the switching lemma (which bounds
decision-tree depth) to the iterative circuit reduction (which needs bounded-width
CNFs/DNFs at each level).

## Union bound for multiple gates

- `switching_bernoulli_union_bound`: For `s` gates, by a union bound, the
  probability that *any* gate fails to reduce is at most
  `s · ((1/2)^l + exp(-np/3))`.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section

namespace LMN

variable {n : ℕ}

/-! ## Monotonicity of bernoulliRestrProb -/

/-- `bernoulliRestrProb` is monotone: if `A ρ → B ρ` for all `ρ`, then
    `bernoulliRestrProb p A ≤ bernoulliRestrProb p B`. -/
lemma bernoulliRestrProb_mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Restriction n → Prop) [DecidablePred A] [DecidablePred B]
    (h : ∀ ρ, A ρ → B ρ) :
    bernoulliRestrProb p A ≤ bernoulliRestrProb p B := by
  unfold bernoulliRestrProb
  apply Finset.sum_le_sum
  intro ρ _
  by_cases ha : A ρ
  · simp [ha, h ρ ha]
  · simp [ha]; split_ifs <;> simp [bernoulliRestrWeight_nonneg' p hp hp1 ρ]

/-! ## Gate switching: DNF → CNF representation -/

/-- After a Bernoulli(`p`) restriction with `p ≤ 1/(40w)`, a width-`w` DNF `g`
    can be expressed as a CNF of width at most `l` with high probability.

    More precisely: the probability that `g|_ρ` does NOT have a width-`l` CNF
    representation is at most `(1/2)^l + exp(-np/3)`.

    This follows immediately from:
    1. `switching_bernoulli_dtDepth_dnf`: `Pr[dtDepth(g|_ρ) > l] ≤ (1/2)^l + exp(-np/3)`
    2. `dtDepth_le_implies_small_dnf_cnf`: `dtDepth ≤ l → ∃ ψ : CNF, ψ.width ≤ l ∧ ...`

    The contrapositive gives us: if no width-`l` CNF exists, then `dtDepth > l`. -/
theorem switching_bernoulli_gate_to_cnf (g : DNF n) (w l : ℕ)
    (hw : g.width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ t ∈ g, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ g, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ¬ ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, ψ.eval x = restrictFn g.eval ρ x) ≤
    (1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3)) := by
  -- The event "no width-l CNF exists" implies "dtDepth > l"
  apply le_trans _ (switching_bernoulli_dtDepth_dnf g w hw hw_pos hnd hnodup hn p hp_pos hp_le hp1 l)
  apply bernoulliRestrProb_mono p hp_pos.le hp1
  intro ρ h_no_cnf
  -- If dtDepth(g|_ρ) ≤ l, then by dtDepth_le_implies_small_dnf_cnf,
  -- there exists a width-≤-l CNF. Contradiction.
  by_contra h_not_gt
  push_neg at h_not_gt
  exact h_no_cnf (dtDepth_le_implies_small_dnf_cnf _ l h_not_gt).2

/-- The dual: after a Bernoulli(`p`) restriction with `p ≤ 1/(40w)`, a width-`w`
    CNF gate can be expressed as a DNF of width at most `l` with high probability. -/
theorem switching_bernoulli_gate_to_dnf_from_cnf (g : CNF n) (w l : ℕ)
    (hw : g.width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ c ∈ g, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ c ∈ g, c.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ¬ ∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = restrictFn (CNF.eval g) ρ x) ≤
    (1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3)) := by
  apply le_trans _ (switching_bernoulli_dtDepth_cnf g w hw hw_pos hnd hnodup hn p hp_pos hp_le hp1 l)
  apply bernoulliRestrProb_mono p hp_pos.le hp1
  intro ρ h_no_dnf
  by_contra h_not_gt
  push_neg at h_not_gt
  exact h_no_dnf (dtDepth_le_implies_small_dnf_cnf _ l h_not_gt).1

/-! ## Corollary: dtDepth bound implies representability -/

/-- If `dtDepth(f|_ρ) ≤ l`, then `f|_ρ` can be expressed as both a width-`l`
    DNF and a width-`l` CNF. This is just a convenient repackaging of
    `dtDepth_le_implies_small_dnf_cnf` for the restricted function. -/
theorem restricted_has_small_cnf_of_dtDepth_le
    (f : (Fin n → Bool) → Bool) (ρ : Restriction n) (l : ℕ)
    (h : dtDepth (restrictFn f ρ) ≤ l) :
    (∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, ψ.eval x = restrictFn f ρ x) :=
  (dtDepth_le_implies_small_dnf_cnf _ l h).2

theorem restricted_has_small_dnf_of_dtDepth_le
    (f : (Fin n → Bool) → Bool) (ρ : Restriction n) (l : ℕ)
    (h : dtDepth (restrictFn f ρ) ≤ l) :
    (∃ φ : DNF n, φ.width ≤ l ∧ ∀ x, φ.eval x = restrictFn f ρ x) :=
  (dtDepth_le_implies_small_dnf_cnf _ l h).1

/-! ## Union bound over multiple gates -/

/-
**Union bound for gate switching.**

    If a circuit has `s` gates (each a width-`w` DNF), the probability that
    *any* gate fails to have decision-tree depth ≤ `l` after a Bernoulli(`p`)
    restriction is at most `s · ((1/2)^l + exp(-np/3))`.

    When this event does not occur, every gate can be replaced by a CNF of
    width at most `l`, yielding a circuit of reduced depth with bounded width.
-/
theorem switching_bernoulli_union_bound
    (gates : Fin s → DNF n) (w l : ℕ)
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ∃ i : Fin s, dtDepth (restrictFn (gates i).eval ρ) > l) ≤
    ↑s * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) := by
      have h_union_bound : (bernoulliRestrProb p (fun ρ => ∃ i, (dtDepth (restrictFn (gates i).eval ρ)) > l)) ≤ ∑ i : Fin s, (bernoulliRestrProb p (fun ρ => (dtDepth (restrictFn (gates i).eval ρ)) > l)) := by
        have h_sum_bound : ∀ (S : Finset (Fin s)) (A : Fin s → Restriction n → Prop) [∀ i, DecidablePred (A i)], bernoulliRestrProb p (fun ρ => ∃ i ∈ S, A i ρ) ≤ ∑ i ∈ S, bernoulliRestrProb p (A i) := by
          intros S AA
          simp [bernoulliRestrProb];
          intros; rw [ Finset.sum_comm ] ; refine' Finset.sum_le_sum fun i hi => _; simp +decide [ Finset.sum_ite ] ;
          split_ifs <;> [ exact le_mul_of_one_le_left ( by exact mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( pow_nonneg ( by linarith ) _ ) ) ( mod_cast Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Classical.choose_spec ( ‹∃ i_1 ∈ S, AA i_1 i› ) |>.1, Classical.choose_spec ( ‹∃ i_1 ∈ S, AA i_1 i› ) |>.2 ⟩ ⟩ ) ; exact mul_nonneg ( Nat.cast_nonneg _ ) ( by exact mul_nonneg ( pow_nonneg ( by linarith ) _ ) ( pow_nonneg ( by linarith ) _ ) ) ];
        simpa using h_sum_bound Finset.univ ( fun i ρ => dtDepth ( restrictFn ( gates i ).eval ρ ) > l );
      refine le_trans h_union_bound ?_;
      convert Finset.sum_le_card_nsmul _ _ _ _ <;> norm_num;
      · ext; norm_num;
      · infer_instance;
      · exact fun i => switching_bernoulli_dtDepth_dnf ( gates i ) w ( hw i ) hw_pos ( hnd i ) ( hnodup i ) hn p hp_pos hp_le hp1 l

/-- When every gate has dtDepth ≤ l under restriction ρ, every gate can be
    replaced by a CNF of width ≤ l. -/
theorem all_gates_have_small_cnf
    (gates : Fin s → DNF n) (l : ℕ) (ρ : Restriction n)
    (h : ∀ i : Fin s, dtDepth (restrictFn (gates i).eval ρ) ≤ l) :
    ∀ i : Fin s, ∃ ψ : CNF n, ψ.width ≤ l ∧
      ∀ x, ψ.eval x = restrictFn (gates i).eval ρ x :=
  fun i => restricted_has_small_cnf_of_dtDepth_le _ ρ l (h i)

/-! ## Step 5: Union bound for CNF-replaceability at layer 2 -/

/-
**Step 5 (union bound for layer-2 CNF-replaceability).**

Let `gates` be the `s₂` DNF gates at layer 2 of a circuit, each of width ≤ `w`.
Under a Bernoulli(`p`) restriction with `p ≤ 1/(40w)`, the probability that
*not all* gates are replaceable by width-`l` CNFs is at most
`s₂ · ((1/2)^l + exp(-np/3))`.

Since `(1/2)^l = 2^{-l}`, this is `s₂ · 2^{-l}` plus a term `s₂ · exp(-np/3)`
that vanishes exponentially as `n → ∞`. For any fixed circuit parameters,
the bound is therefore `< s₂ · 2^{-l} + ε` for all large enough `n`.

The proof applies `switching_bernoulli_gate_to_cnf` to each gate individually
and then a union bound over the `s₂` gates.
-/
theorem layer2_cnf_replaceability_union_bound
    (gates : Fin s₂ → DNF n) (w l : ℕ)
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ∃ i : Fin s₂,
        ¬ ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, ψ.eval x = restrictFn (gates i).eval ρ x) ≤
    ↑s₂ * ((1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3))) := by
  refine' le_trans _ ( switching_bernoulli_union_bound gates w l _ _ _ _ _ _ _ _ _ );
  all_goals norm_cast at * ;
  convert bernoulliRestrProb_mono p hp_pos.le hp1 _ _ _ using 3;
  exact fun ρ h => by rcases h with ⟨ i, hi ⟩ ; exact ⟨ i, not_le.mp fun h' => hi <| restricted_has_small_cnf_of_dtDepth_le _ _ _ h' ⟩ ;

/-
**Step 5, simplified form.**

The probability that not all layer-2 gates are replaceable by width-`l` CNFs
is at most `s₂ · 2^{-l}`, where `2^{-l} = (1/2)^l`, plus a term that
vanishes as `n → ∞`.

This is the "clean" form of the union bound: for large enough `n`,
the exponential tail `s₂ · exp(-np/3)` is negligible, and the dominant term is
`s₂ · 2^{-l}`.
-/
theorem layer2_cnf_replaceability_simplified
    (gates : Fin s₂ → DNF n) (w l : ℕ)
    (hw : ∀ i, (gates i).width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ i, ∀ t ∈ gates i, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ i, ∀ t ∈ gates i, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1)
    (ε : ℝ) (_hε : 0 < ε)
    (hn_large : Real.exp (-(↑n * p / 3)) ≤ ε / ↑s₂)
    (hs₂_pos : 0 < s₂) :
    bernoulliRestrProb p
      (fun ρ => ∃ i : Fin s₂,
        ¬ ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, ψ.eval x = restrictFn (gates i).eval ρ x) ≤
    ↑s₂ * (1 / 2 : ℝ) ^ l + ε := by
  have := layer2_cnf_replaceability_union_bound gates w l hw hw_pos hnd hnodup hn p hp_pos hp_le hp1;
  exact this.trans ( by rw [ mul_add ] ; nlinarith [ mul_div_cancel₀ ε ( by positivity : ( s₂ : ℝ ) ≠ 0 ) ] )

end LMN
end