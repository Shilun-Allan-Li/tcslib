/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/

import TCSlib.LearningTheory.Minimax.ConvexMinimaxCore
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.LinearMapPiProd

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Real Finset BigOperators

namespace OnlineLearning

/-!
# Hahn-Banach/Separation Proof for Convex-Compact Minimax

## Main results

- `convex_compact_minimax_by_separation`: convex-compact minimax theorem via the finite-column separation route
- `convex_compact_minimax_of_finite_sublevel_intersections`: minimax identity from finite sublevel intersection property via compactness
- `finite_sublevel_intersections_by_separation`: for each finite column sample and ε > 0, a row exists with payoff at most value + ε on all sampled columns, proved by Hahn-Banach separation normalizing into a mixed column strategy

## References

- Original formalization by Karim Abdel Sadek, Mark Bedaywi
-/

/-- For a finite column sample, this is the set of vectors strictly above one
row's payoff vector on that sample. -/
def finiteUpperImage {Y : Set ℝ} (X : Set ℝ) (f : ℝ → ℝ → ℝ) (u : Finset Y) :
    Set (u → ℝ) :=
  {z | ∃ x ∈ X, ∀ y : u, f x y < z y}

-- Pick any row and add `1` to each sampled payoff.  This gives one point of the
-- upper image, so the set we later separate from is not empty.
lemma finiteUpperImage_nonempty {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (hX : X.Nonempty) (u : Finset Y) :
    (finiteUpperImage X f u).Nonempty := by
  rcases hX with ⟨x, hx⟩
  refine ⟨fun y : u => f x y + 1, x, hx, ?_⟩
  intro y
  linarith

-- If `z` is witnessed by row `x` and `w` by row `x'`, then the convex
-- combination is witnessed by the convex combination of `x` and `x'`.
-- Convexity of `f` in the row variable gives the needed payoff inequality.
lemma finiteUpperImage_convex {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} (u : Finset Y)
    (hX : Convex ℝ X) (hf : ∀ y ∈ Y, ConvexOn ℝ X (fun x => f x y)) :
    Convex ℝ (finiteUpperImage X f u) := by
  intro z hz w hw a b ha hb hab
  rcases hz with ⟨x, hx, hz⟩
  rcases hw with ⟨x', hx', hw⟩
  refine ⟨a • x + b • x', hX hx hx' ha hb hab, ?_⟩
  intro y
  have hconv := (hf (y : Y) (y : Y).2).2 hx hx' ha hb hab
  have hz_y := hz y
  have hw_y := hw y
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hconv hz_y hw_y ⊢
  have hlt : a * f x ↑↑y + b * f x' ↑↑y < a * z y + b * w y := by
    rcases ha.eq_or_lt with rfl | ha_pos
    · have hb_one : b = 1 := by linarith
      nlinarith
    · rcases hb.eq_or_lt with rfl | hb_pos
      · have ha_one : a = 1 := by linarith
        nlinarith
      · have hz_mul := mul_lt_mul_of_pos_left hz_y ha_pos
        have hw_mul := mul_lt_mul_of_pos_left hw_y hb_pos
        nlinarith
  exact hconv.trans_lt hlt

-- The upper image is coordinatewise upward closed.  The same witness row still
-- works after increasing any coordinates.
lemma finiteUpperImage_upper {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {z : u → ℝ} (hz : z ∈ finiteUpperImage X f u) {z' : u → ℝ}
    (hzz' : ∀ y : u, z y ≤ z' y) :
    z' ∈ finiteUpperImage X f u := by
  rcases hz with ⟨x, hx, hz⟩
  exact ⟨x, hx, fun y => (hz y).trans_le (hzz' y)⟩

-- For a fixed row, membership is just finitely many strict inequalities
-- `f x y < z y`.  The upper image is the union of these open sets over `x ∈ X`.
lemma finiteUpperImage_isOpen {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} (u : Finset Y) :
    IsOpen (finiteUpperImage X f u) := by
  classical
  have hrepr :
      finiteUpperImage X f u =
        ⋃ x : X,
          ({z : u → ℝ | ∀ y : u, f (x : ℝ) (y : ℝ) < z y} : Set (u → ℝ)) := by
    ext z
    simp [finiteUpperImage]
  rw [hrepr]
  apply isOpen_iUnion
  intro x
  rw [show ({z : u → ℝ | ∀ y : u, f (x : ℝ) (y : ℝ) < z y} : Set (u → ℝ)) =
      ⋂ y : u, (fun z : u → ℝ => z y) ⁻¹' Set.Ioi (f (x : ℝ) (y : ℝ)) by
    ext z
    simp]
  exact isOpen_iInter_of_finite fun y : u =>
    isOpen_Ioi.preimage (continuous_apply y)

-- This expands a linear functional on a finite product into its coordinate
-- coefficients.  Those coefficients are what we normalize into probabilities.
lemma continuousLinearMap_pi_apply_eq_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (z : ι → ℝ) :
    L z = ∑ i : ι, z i * L (Pi.single i (1 : ℝ)) := by
  rw [← ContinuousLinearMap.sum_comp_single (R := ℝ) (φ := fun _ : ι => ℝ) L z]
  apply Finset.sum_congr rfl
  intro i _
  change L (Pi.single (M := fun _ : ι => ℝ) i (z i)) =
    z i * L (Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ))
  have hsingle :
      Pi.single (M := fun _ : ι => ℝ) i (z i) =
        (z i) • Pi.single (M := fun _ : ι => ℝ) i (1 : ℝ) := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Pi.single_eq_of_ne hji]
  rw [hsingle, map_smul]
  simp [smul_eq_mul]

-- No coordinate coefficient of the separator can be positive.  If one were
-- positive, we could move an upper-image point far upward in that coordinate;
-- the point would remain in the upper image but its `L`-value would pass
-- `L cvec`, contradicting separation.
lemma separating_coordinate_nonpos {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    ∀ y : u, L (Pi.single y (1 : ℝ)) ≤ 0 := by
  classical
  intro y
  by_contra hnot
  have hpos : 0 < L (Pi.single y (1 : ℝ)) := lt_of_not_ge hnot
  rcases finiteUpperImage_nonempty (X := X) (Y := Y) (f := f) hX u with ⟨z, hz⟩
  let t := (L cvec - L z + 1) / L (Pi.single y (1 : ℝ))
  have ht_nonneg : 0 ≤ t := by
    have hnum : 0 ≤ L cvec - L z + 1 := by
      have := hsep z hz
      linarith
    exact div_nonneg hnum hpos.le
  have hz' :
      z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ) ∈ finiteUpperImage X f u := by
    refine finiteUpperImage_upper hz ?_
    intro y'
    by_cases hyy' : y' = y
    · subst hyy'
      simp [ht_nonneg]
    · simp [Pi.single_eq_of_ne hyy']
  have hlt := hsep (z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ)) hz'
  have hcalc : L (z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ)) = L cvec + 1 := by
    simp [t, map_add, map_smul, smul_eq_mul, hpos.ne']
    field_simp [hpos.ne']
    ring
  rw [hcalc] at hlt
  linarith

-- The separator is genuinely nonzero: the zero functional cannot be strictly
-- smaller on every upper-image point than on `cvec`.
lemma separating_functional_ne_zero {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    L ≠ 0 := by
  intro hL
  rcases finiteUpperImage_nonempty (X := X) (Y := Y) (f := f) hX u with ⟨z, hz⟩
  simpa [hL] using hsep z hz

-- The coordinate coefficients are all nonpositive and not all zero.  Therefore
-- their negatives have positive total mass, which lets us divide by this mass
-- and get a probability vector.
lemma separating_weight_sum_pos {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    0 < ∑ y : u, -L (Pi.single y (1 : ℝ)) := by
  classical
  have hnonpos := separating_coordinate_nonpos (X := X) (Y := Y) (f := f) hX L hsep
  have hnonneg : ∀ y : u, 0 ≤ -L (Pi.single y (1 : ℝ)) := by
    intro y
    linarith [hnonpos y]
  have hne : ∃ y : u, L (Pi.single y (1 : ℝ)) ≠ 0 := by
    by_contra hnone
    have hall : ∀ y : u, L (Pi.single y (1 : ℝ)) = 0 := by
      intro y
      exact not_not.mp (by
        simpa using (show ¬ L (Pi.single y (1 : ℝ)) ≠ 0 from fun hy => hnone ⟨y, hy⟩))
    have hLzero : L = 0 := by
      ext z
      rw [continuousLinearMap_pi_apply_eq_sum_single L z]
      simp [hall]
    exact separating_functional_ne_zero (X := X) (Y := Y) (f := f) hX L hsep hLzero
  rcases hne with ⟨y, hy⟩
  have hpos_y : 0 < -L (Pi.single y (1 : ℝ)) := by
    have hle := hnonpos y
    have hlt : L (Pi.single y (1 : ℝ)) < 0 := lt_of_le_of_ne hle hy
    linarith
  exact Finset.sum_pos' (fun i _ => hnonneg i) ⟨y, Finset.mem_univ y, hpos_y⟩

-- This is the key separation lemma.  For every finite set of columns, there is
-- a row whose payoff is at most `value + ε` on all columns in that finite set.
-- The contradiction case is what turns a separating hyperplane into a mixed
-- column strategy.
set_option linter.flexible false in
lemma finite_sublevel_intersections_by_separation {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    ∀ ε > 0, ∀ u : Finset Y,
      (X ∩ ⋂ y ∈ u,
        minimaxSublevel X f (y : ℝ) ((⨆ y : Y, ⨅ x : X, f x y) + ε)).Nonempty := by
  classical
  intro ε hε u
  let v : ℝ := ⨆ y : Y, ⨅ x : X, f x y
  let c : ℝ := v + ε
  let cvec : u → ℝ := fun _ => c
  by_cases hc : cvec ∈ finiteUpperImage X f u
  -- Easy case: membership of the constant vector gives a row with
  -- `f x y < c` on every sampled column, which is stronger than the sublevel
  -- condition we need.
  · rcases hc with ⟨x, hxX, hxlt⟩
    refine ⟨x, hxX, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro y
    refine Set.mem_iInter.mpr ?_
    intro hyu
    exact ⟨hxX, (hxlt ⟨y, hyu⟩).le⟩
  -- Hard case: the constant vector is outside the open convex upper image.
  -- Separation gives a functional `L`; the previous lemmas show that
  -- `-L(e_y)` can be normalized into weights on the sampled columns.
  · obtain ⟨L, hsep⟩ :=
      geometric_hahn_banach_open_point
        (finiteUpperImage_convex (X := X) (Y := Y) (f := f) u h.X_convex h.convex_left)
        (finiteUpperImage_isOpen (X := X) (Y := Y) (f := f) u) hc
    let W : ℝ := ∑ y : u, -L (Pi.single y (1 : ℝ))
    have hWpos : 0 < W :=
      separating_weight_sum_pos (X := X) (Y := Y) (f := f) h.X_nonempty L hsep
    let q : u → ℝ := fun y => -L (Pi.single y (1 : ℝ)) / W
    have hcoord_nonpos :
        ∀ y : u, L (Pi.single y (1 : ℝ)) ≤ 0 :=
      separating_coordinate_nonpos (X := X) (Y := Y) (f := f) h.X_nonempty L hsep
    have hq_nonneg : ∀ y : u, 0 ≤ q y := by
      intro y
      exact div_nonneg (by linarith [hcoord_nonpos y]) hWpos.le
    have hq_sum : ∑ y : u, q y = 1 := by
      calc
        ∑ y : u, q y = (∑ y : u, -L (Pi.single y (1 : ℝ))) / W := by
          simp [q, div_eq_mul_inv, Finset.sum_mul]
        _ = W / W := rfl
        _ = 1 := div_self hWpos.ne'
    -- Algebraic heart of the proof.  For a fixed row `x`, the vector
    -- `f x y + δ` lies in the upper image.  Applying separation to this vector,
    -- expanding `L` in coordinates, and multiplying by the negative number
    -- `-1 / W` gives `c < average payoff + δ`.  Since `δ > 0` is arbitrary,
    -- we get the non-strict inequality below.
    have hsep_le : ∀ x ∈ X, c ≤ ∑ y : u, q y * f x (y : ℝ) := by
      intro x hxX
      apply le_of_forall_pos_le_add
      intro δ hδ
      let zδ : u → ℝ := fun y => f x (y : ℝ) + δ
      have hzδ : zδ ∈ finiteUpperImage X f u := by
        exact ⟨x, hxX, fun y => by simp [zδ, hδ]⟩
      have hlt := hsep zδ hzδ
      have hLz :
          L zδ = ∑ y : u, (f x (y : ℝ) + δ) * L (Pi.single y (1 : ℝ)) := by
        exact continuousLinearMap_pi_apply_eq_sum_single L zδ
      have hLc : L cvec = ∑ y : u, c * L (Pi.single y (1 : ℝ)) := by
        exact continuousLinearMap_pi_apply_eq_sum_single L cvec
      rw [hLz, hLc] at hlt
      have hineq :
          c < ∑ y : u, q y * f x (y : ℝ) + δ := by
        let S : ℝ := ∑ y : u, L (Pi.single y (1 : ℝ))
        have hS : S = -W := by
          simp [S, W]
        have hone : (-1 / W) * S = 1 := by
          rw [hS]
          field_simp [hWpos.ne']
        have hrewrite :
            ∑ y : u, q y * f x (y : ℝ) + δ =
              (-1 / W) * ∑ y : u, (f x (y : ℝ) + δ) * L (Pi.single y (1 : ℝ)) := by
          calc
            ∑ y : u, q y * f x (y : ℝ) + δ =
                (-1 / W) * (∑ y : u, f x (y : ℝ) * L (Pi.single y (1 : ℝ))) +
                  δ * ((-1 / W) * S) := by
              rw [hone]
              simp [q, div_eq_mul_inv, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring_nf
            _ = (-1 / W) *
                ∑ y : u, (f x (y : ℝ) + δ) * L (Pi.single y (1 : ℝ)) := by
              simp [S, Finset.mul_sum]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro y _
              ring_nf
        have hc_rewrite :
            c = (-1 / W) * ∑ y : u, c * L (Pi.single y (1 : ℝ)) := by
          calc
            c = c * ((-1 / W) * S) := by rw [hone]; ring_nf
            _ = (-1 / W) * ∑ y : u, c * L (Pi.single y (1 : ℝ)) := by
              simp [S, Finset.mul_sum]
              ring_nf
        rw [hrewrite, hc_rewrite]
        have hneg : (-1 / W : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) hWpos
        exact mul_lt_mul_of_neg_left hlt hneg
      exact hineq.le
    -- The weights `q` are a probability distribution on the sampled columns.
    -- Convexity of `Y` makes their weighted average `ybar` an actual point of
    -- `Y`, and concavity in the column variable gives Jensen's inequality:
    -- average payoff at the sampled columns is at most payoff at `ybar`.
    let ybar : ℝ := ∑ y : u, q y * (y : ℝ)
    have hybar : ybar ∈ Y := by
      simpa [ybar, smul_eq_mul] using
        h.Y_convex.sum_mem (t := Finset.univ) (w := q) (z := fun y : u => (y : ℝ))
          (fun y _ => hq_nonneg y) (by simpa using hq_sum) (fun y _ => (y : Y).2)
    have hforall_x : ∀ x : X, c ≤ f x ybar := by
      intro x
      have hleft := hsep_le (x : ℝ) x.2
      have hconc :
          (∑ y : u, q y * f (x : ℝ) (y : ℝ)) ≤ f (x : ℝ) ybar := by
        simpa [ybar, smul_eq_mul] using
          (h.concave_right (x : ℝ) x.2).le_map_sum
            (t := Finset.univ) (w := q) (p := fun y : u => (y : ℝ))
            (fun y _ => hq_nonneg y) (by simpa using hq_sum) (fun y _ => (y : Y).2)
      exact hleft.trans hconc
    -- Thus the same column `ybar` satisfies `c ≤ f x ybar` for every row.
    -- Hence `c ≤ inf_x f x ybar ≤ sup_y inf_x f x y = v`, contradicting
    -- `c = v + ε`.
    have hinf : c ≤ ⨅ x : X, f x ybar := by
      haveI : Nonempty X := h.X_nonempty.to_subtype
      exact le_ciInf hforall_x
    have hbddAbove_inf : BddAbove (Set.range fun y : Y => ⨅ x : X, f x y) := by
      rcases h.bounded_above with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      rintro _ ⟨y, rfl⟩
      have hbelow_y : BddBelow (Set.range fun x : X => f x y) := by
        rcases h.bounded_below with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rintro _ ⟨x, rfl⟩
        exact ha ⟨(x, y), rfl⟩
      exact (ciInf_le hbelow_y (Classical.choice h.X_nonempty.to_subtype)).trans
        (hb ⟨(Classical.choice h.X_nonempty.to_subtype, y), rfl⟩)
    have hle_v : c ≤ v := by
      let hybar_sub : Y := ⟨ybar, hybar⟩
      exact hinf.trans (le_ciSup hbddAbove_inf hybar_sub)
    have : v + ε ≤ v := by simpa [c] using hle_v
    linarith

-- This packages the compactness argument.  If every finite set of sublevel
-- constraints is satisfiable, compactness of `X` gives one row satisfying all
-- column constraints at level `value + ε`.  Letting `ε` go to zero gives the
-- hard minimax inequality.
theorem convex_compact_minimax_of_finite_sublevel_intersections {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (hfin : ∀ ε > 0, ∀ u : Finset Y,
      (X ∩ ⋂ y ∈ u,
        minimaxSublevel X f y ((⨆ y : Y, ⨅ x : X, f x y) + ε)).Nonempty) :
    ConvexCompactMinimaxStatement X Y f := by
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  unfold ConvexCompactMinimaxStatement
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, hx_le⟩ :=
      exists_forall_le_of_finite_sublevel_intersections h
        ((⨆ y : Y, ⨅ x : X, f x y) + ε) (hfin ε hε)
    let xX : X := ⟨x, hx⟩
    -- The compactness point works for all columns, so the supremum over columns
    -- at this row is at most the lower value plus `ε`.
    have hsup_le :
        (⨆ y : Y, f xX y) ≤ (⨆ y : Y, ⨅ x : X, f x y) + ε := by
      exact ciSup_le fun y => hx_le y
    have hleft_le : (⨅ x : X, ⨆ y : Y, f x y) ≤ ⨆ y : Y, f xX y := by
      have hbdd : BddBelow (Set.range fun x' : X => ⨆ y : Y, f x' y) := by
        rcases h.bounded_below with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        rintro _ ⟨x', rfl⟩
        let y₀ : Y := Classical.choice ‹Nonempty Y›
        have habove : BddAbove (Set.range fun y : Y => f x' y) := by
          rcases h.bounded_above with ⟨b, hb⟩
          refine ⟨b, ?_⟩
          rintro _ ⟨y, rfl⟩
          exact hb ⟨(x', y), rfl⟩
        exact (ha ⟨(x', y₀), rfl⟩).trans (le_ciSup habove y₀)
      exact ciInf_le hbdd xX
    exact hleft_le.trans hsup_le
  -- The reverse inequality is the standard weak minimax inequality from the
  -- core file.
  · exact weak_convex_compact_minimax h

/-- Final convex-compact minimax theorem using the finite-column separation route. -/
theorem convex_compact_minimax_by_separation {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    ConvexCompactMinimaxStatement X Y f := by
  exact convex_compact_minimax_of_finite_sublevel_intersections h
    (finite_sublevel_intersections_by_separation h)

end OnlineLearning
