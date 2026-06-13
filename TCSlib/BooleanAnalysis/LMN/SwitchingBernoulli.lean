import TCSlib.BooleanAnalysis.Switching
import TCSlib.BooleanAnalysis.LMN.BernoulliCost
import Mathlib

/-!
# Bernoulli Switching Lemma (Step 3 of LMN)

This file proves that under a Bernoulli(`p`) random restriction with `p ≤ 1/(40w)`,
a width-`w` DNF (or CNF) formula has decision-tree depth exceeding `t` with
probability at most `(1/2)^t + exp(-np/3)`.

This is the "Bernoulli version" of Håstad's Switching Lemma, derived from the
counting version (`SwitchingLemma2.switching_lemma`) and the Bernoulli
restriction cost theorem (`BernoulliCost.bernoulli_restriction_cost`).

## Mathematical argument

1. **Counting Switching Lemma** gives: for fixed-size `k`-restrictions,
   `Pr_{R_k}[dtDepth > d] ≤ (10kw/n)^d` when `5k ≤ n`.

2. For `5k > n`, the bound `(10kw/n)^d ≥ 1 ≥ Pr_{R_k}[dtDepth > d]` holds trivially
   (since `10kw/n ≥ 2w ≥ 2` when `w ≥ 1` and `k > n/5`).

3. Writing `(10kw/n)^d = (5k · (2w) / n)^d`, we apply `bernoulli_restriction_cost`
   with `w' = 2w` to obtain:
   `Pr_{R_p}[dtDepth > d] ≤ (20pw)^d + exp(-np/3)`

4. For `p ≤ 1/(40w)`, we get `(20pw)^d ≤ (1/2)^d`.

## Main results

- `switching_bernoulli_dtDepth_dnf`: Bernoulli switching lemma for DNFs
- `switching_bernoulli_dtDepth_cnf`: Bernoulli switching lemma for CNFs
-/

open SwitchingLemma2 BernoulliCost
open Classical in
attribute [local instance] Classical.propDecidable

noncomputable section

namespace SwitchingBernoulli

variable {n : ℕ}

/-! ## Bridge: counting → fixedSizeRestrProb -/

/-
The cardinality of `fixedSizeRestrs n k` equals `numSRestrictions n k`
    (= `C(n,k) · 2^{n-k}`).
-/
lemma fixedSizeRestrs_card (k : ℕ) (hk : k ≤ n) :
    (fixedSizeRestrs n k).card = numSRestrictions n k := by
  have h_card : (Finset.univ.filter fun ρ : Fin n → Option Bool => (Finset.univ.filter fun i => ρ i = none).card = k).card = (Nat.choose n k) * 2^(n-k) := by
    -- Let's count the number of restrictions with exactly k free variables by considering the number of ways to choose k positions out of n to be free.
    have h_count : (Finset.univ.filter (fun ρ : Fin n → Option Bool => (Finset.univ.filter (fun i => ρ i = none)).card = k)).card = Finset.sum (Finset.powersetCard k (Finset.univ : Finset (Fin n))) (fun s => 2 ^ (n - s.card)) := by
      have h_count : Finset.univ.filter (fun ρ : Fin n → Option Bool => (Finset.univ.filter (fun i => ρ i = none)).card = k) = Finset.biUnion (Finset.powersetCard k (Finset.univ : Finset (Fin n))) (fun s => Finset.image (fun f : { i : Fin n // i ∉ s } → Bool => fun i => if h : i ∈ s then none else some (f ⟨i, h⟩)) (Finset.univ : Finset ({ i : Fin n // i ∉ s } → Bool))) := by
        ext ρ; simp [Finset.mem_biUnion, Finset.mem_image];
        constructor <;> intro h;
        · refine' ⟨ Finset.univ.filter fun i => ρ i = none, _, _ ⟩ <;> simp_all +decide [ funext_iff ];
          use fun ⟨i, hi⟩ => if h : ρ i = none then Bool.true else (ρ i).get (by
          cases h' : ρ i <;> aesop)
          generalize_proofs at *;
          grind;
        · obtain ⟨ a, ha, b, rfl ⟩ := h; simp +decide [ Finset.filter_congr, ha ] ;
      rw [ h_count, Finset.card_biUnion ];
      · refine' Finset.sum_congr rfl fun s hs => _;
        rw [ Finset.card_image_of_injective ];
        · simp +decide [ Finset.card_univ ];
        · intro f g hfg; ext i; replace hfg := congr_fun hfg i; aesop;
      · intros s hs t ht hst; simp_all +decide [ Finset.disjoint_left ] ;
        intro a x hx; contrapose! hst; ext i; replace hx := congr_fun hx i; by_cases hi : i ∈ s <;> by_cases hj : i ∈ t <;> simp_all +decide ;
    rw [ h_count, Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ Finset.card_univ ];
  convert h_card using 1;
  convert Finset.card_image_of_injective _ ( show Function.Injective ( fun ρ : Restriction n => fun i => ρ i ) from fun a b h => by funext i; exact congr_fun h i ) using 2;
  ext; simp [fixedSizeRestrs];
  convert Iff.rfl;
  ext; simp [Restriction.freeVars]

/-
The filter of `fixedSizeRestrs` by `IsBadRestriction` equals the counting
    switching lemma's filter.
-/
lemma fixedSizeRestrs_filter_bad_eq (f : (Fin n → Bool) → Bool) (d k : ℕ) :
    ((fixedSizeRestrs n k).filter (fun ρ => dtDepth (restrictFn f ρ) > d)).card =
    (Finset.univ.filter (fun ρ : Restriction n =>
      IsRestriction k ρ ∧ IsBadRestriction f d ρ)).card := by
  congr 1 with ρ ; simp +decide [ IsRestriction, IsBadRestriction ] ;
  simp +decide [ fixedSizeRestrs, Restriction.numFree ]

/-
From the counting switching lemma: `fixedSizeRestrProb(dtDepth > d)(k) ≤ (10kw/n)^d`
    when `5k ≤ n`.
-/
lemma switching_fixedSize_bound_small (f : DNF n) (w k d : ℕ)
    (hn : 0 < n) (hw : f.width ≤ w)
    (hk : 5 * k ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    fixedSizeRestrProb (fun ρ => dtDepth (restrictFn f.eval ρ) > d) k ≤
    (10 * ↑k * ↑w / ↑n) ^ d := by
  convert SwitchingLemma2.switching_lemma hn f w k d hw hk hnd hnodup using 1;
  rw [ fixedSizeRestrProb ];
  rw [ div_pow, div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ fixedSizeRestrs_card ];
  · rw [ mul_comm, fixedSizeRestrs_filter_bad_eq, fixedSizeRestrs_card ];
    · grind +qlia;
    · linarith;
  · refine' ⟨ fun i => if i.val < k then none else some Bool.true, _ ⟩ ; simp +decide [ fixedSizeRestrs ];
    rw [ show ( Restriction.freeVars fun i : Fin n => if ( i : ℕ ) < k then none else some true ) = Finset.univ.filter ( fun i : Fin n => ( i : ℕ ) < k ) from ?_ ];
    · rw [ Finset.card_eq_of_bijective ];
      use fun i hi => ⟨ i, by linarith ⟩;
      · grind +splitIndPred;
      · grind +qlia;
      · grind +extAll;
    · ext i; simp [Restriction.freeVars];
  · positivity

/-
For all `k ≤ n`, `fixedSizeRestrProb(dtDepth > d)(k) ≤ (10kw/n)^d`.
    For `5k > n`, uses the trivial bound since `10kw/n ≥ 2 ≥ 1`.
-/
lemma switching_fixedSize_bound (f : DNF n) (w k d : ℕ)
    (hn : 0 < n) (hw : f.width ≤ w) (hw_pos : 0 < w)
    (_hk : k ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    fixedSizeRestrProb (fun ρ => dtDepth (restrictFn f.eval ρ) > d) k ≤
    (10 * ↑k * ↑w / ↑n) ^ d := by
  -- We split into two cases: $5k \le n$ and $5k > n$.
  by_cases h_case : 5 * k ≤ n;
  · exact switching_fixedSize_bound_small f w k d hn hw h_case hnd hnodup;
  · exact le_trans ( fixedSizeRestrProb_le_one _ _ ) ( one_le_pow₀ ( by rw [ le_div_iff₀ ] <;> norm_cast ; nlinarith ) )

/-- Rewrite the bound `(10kw/n)^d = (5k · (2w) / n)^d` to match
    `bernoulli_restriction_cost`'s hypothesis format. -/
lemma switching_fixedSize_bound_rescaled (f : DNF n) (w k d : ℕ)
    (hn : 0 < n) (hw : f.width ≤ w) (hw_pos : 0 < w)
    (hk : k ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    fixedSizeRestrProb (fun ρ => dtDepth (restrictFn f.eval ρ) > d) k ≤
    (5 * ↑k * ↑(2 * w) / ↑n) ^ d := by
  have h := switching_fixedSize_bound f w k d hn hw hw_pos hk hnd hnodup
  convert h using 2
  push_cast
  ring

/-! ## Main results -/

/-
**Bernoulli switching lemma for decision-tree depth (DNF version).**

For a width-`w` DNF `f` under a Bernoulli(`p`) random restriction with
`p ≤ 1/(40w)`, the probability that the restricted function has decision-tree
depth exceeding `t` is at most `(1/2)^t + exp(-np/3)`.

The `(1/2)^t` term comes from the switching lemma applied with the
Bernoulli cost reduction, and `exp(-np/3)` is the Chernoff tail for
the unlikely event that the restriction leaves too many variables free.
-/
theorem switching_bernoulli_dtDepth_dnf (f : DNF n) (w : ℕ)
    (hw : f.width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1)
    (t : ℕ) :
    bernoulliRestrProb p
      (fun ρ => dtDepth (restrictFn f.eval ρ) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p / 3)) := by
  by_cases ht : t = 0;
  · convert bernoulliRestrProb_le_one' p hp_pos.le hp1 _ |> le_trans <| ?_ using 1 ; norm_num [ ht ];
    positivity;
  · have := bernoulli_restriction_cost hn p hp_pos hp1 ( 2 * w ) t ( by positivity ) ( by positivity ) ( fun ρ => dtDepth ( restrictFn f.eval ρ ) > t ) ?_;
    · refine le_trans this ?_;
      exact add_le_add ( pow_le_pow_left₀ ( by positivity ) ( by rw [ le_div_iff₀ ( by positivity ) ] at hp_le; push_cast at *; nlinarith [ show ( w : ℝ ) ≥ 1 by norm_cast ] ) _ ) le_rfl;
    · intro k hk;
      convert switching_fixedSize_bound_rescaled f w k t hn hw hw_pos hk hnd hnodup using 1

/-
**Bernoulli switching lemma for CNFs.**

Same as `switching_bernoulli_dtDepth_dnf` but for CNF formulas.
-/
theorem switching_bernoulli_dtDepth_cnf (f : CNF n) (w : ℕ)
    (hw : f.width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ c ∈ f, ∀ l₁ ∈ c, ∀ l₂ ∈ c, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ c ∈ f, c.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1)
    (t : ℕ) :
    bernoulliRestrProb p
      (fun ρ => dtDepth (restrictFn (CNF.eval f) ρ) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p / 3)) := by
  -- Apply the switching lemma for DNFs to the dual DNF of f.
  have h_dual : bernoulliRestrProb p (fun ρ => dtDepth (restrictFn (cnfToDualDNF f).eval ρ) > t) ≤ (1 / 2 : ℝ) ^ t + Real.exp (-(n * p / 3)) := by
    apply SwitchingBernoulli.switching_bernoulli_dtDepth_dnf;
    convert hw using 1;
    any_goals assumption;
    · exact cnfToDualDNF_width f;
    · convert SwitchingLemmaCNF.cnfToDualDNF_inj f hnd using 1;
    · exact fun t a => SwitchingLemmaCNF.cnfToDualDNF_nodup f hnodup t a;
  convert h_dual using 1;
  -- By definition of `cnfToDualDNF`, we have `restrictFn f.eval ρ = fun x => !(restrictFn (cnfToDualDNF f).eval ρ x)`.
  have h_restrict : ∀ ρ : Restriction n, restrictFn f.eval ρ = fun x => !(restrictFn (cnfToDualDNF f).eval ρ x) := by
    intro ρ; funext x; simp +decide [ restrictFn, cnfToDualDNF_eval ] ;
  simp +decide only [h_restrict, dtDepth_neg]

end SwitchingBernoulli

end