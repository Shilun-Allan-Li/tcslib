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

/-!
# Hahn-Banach/Separation Proof for Convex-Compact Minimax

This file proves the convex-compact minimax theorem [CBL06, Thm 7.1] (specialized to
subsets of `ℝ`) unconditionally. **Route deviation:** the source proves the theorem by a
no-regret argument; in `TCSlib.LearningTheory.Minimax.ConvexMinimaxNoRegret` the last step
of that argument is isolated as `Theorem71CompactApproximation`, which is not derived there
from the theorem's hypotheses alone but proved under uniform equicontinuity in the row
variable or joint continuity on compact `X × Y` (no claim is made that the source's
argument is wrong). The proof here instead separates a constant vector from
the open convex "upper image" of a finite column sample by Hahn–Banach, normalizes the
separating functional into a mixed column strategy, uses concavity in the column variable
to turn it into a single column point, and finishes with the finite-intersection property
of the compact row set. Komiya's elementary proof of Sion's theorem [Kom88] is a
different route to a more general result (compact convex `X` in a linear topological
space); this file does not follow Komiya's argument either.

## Main definitions

- `finiteUpperImage`: for a finite column sample, the set of vectors strictly above some
  row's payoff vector on that sample.

## Main results

- `convex_compact_minimax_by_separation`: the convex-compact minimax theorem via the
  finite-column separation route.
- `convex_compact_minimax_of_finite_sublevel_intersections`: the minimax identity from the
  finite sublevel intersection property, via compactness.
- `finite_sublevel_intersections_by_separation`: for each finite column sample and
  `ε > 0`, a row exists with payoff at most `value + ε` on all sampled columns, proved by
  Hahn–Banach separation normalizing into a mixed column strategy.
- `separating_functional_normalized_le`: the algebraic heart of the separation step.

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*,
  Cambridge University Press, 2006. Chapter 7 (Theorem 7.1).
* [Kom88] H. Komiya, "Elementary proof for Sion's minimax theorem",
  *Kodai Math. J.* 11(1):5–7, 1988.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

namespace OnlineLearning

/-- The upper image of a finite column sample `u`: the set of vectors `z : u → ℝ` that
lie strictly above the payoff vector `y ↦ f x y` of some row `x ∈ X` in every sampled
coordinate. -/
def finiteUpperImage {Y : Set ℝ} (X : Set ℝ) (f : ℝ → ℝ → ℝ) (u : Finset Y) :
    Set (u → ℝ) :=
  {z | ∃ x ∈ X, ∀ y : u, f x y < z y}

/-- The upper image of a finite column sample is nonempty when `X` is: pick any row and
add `1` to each sampled payoff. -/
lemma finiteUpperImage_nonempty {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (hX : X.Nonempty) (u : Finset Y) :
    (finiteUpperImage X f u).Nonempty := by
  rcases hX with ⟨x, hx⟩
  refine ⟨fun y : u => f x y + 1, x, hx, ?_⟩
  intro y
  linarith

/-- The upper image of a finite column sample is convex when `X` is convex and `f` is
convex in the row variable: if `z` is witnessed by the row `x` and `w` by the row `x'`,
then the convex combination `a z + b w` is witnessed by the row `a x + b x'`, since
convexity of `f` in the row variable gives `f (a x + b x') y ≤ a f x y + b f x' y`.

**Proof sketch.** Let `z` be witnessed by the row `x` and `w` by the row `x'`, and let
`a, b ≥ 0` with `a + b = 1`. Step 1: the row `a x + b x'` lies in `X` by convexity of `X`.
Step 2: for each sampled column `y`, convexity of `f(·, y)` on `X` gives
`f (a x + b x') y ≤ a f x y + b f x' y`. Step 3: the strict witness inequalities
`f x y < z y` and `f x' y < w y` combine to `a f x y + b f x' y < a z y + b w y`, by cases
on whether `a = 0` (so `b = 1`), `b = 0` (so `a = 1`), or both are positive (scale each
inequality by its positive weight and add). Step 4: chain Steps 2 and 3. -/
lemma finiteUpperImage_convex {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} (u : Finset Y)
    (hX : Convex ℝ X) (hf : ∀ y ∈ Y, ConvexOn ℝ X (fun x => f x y)) :
    Convex ℝ (finiteUpperImage X f u) := by
  intro z hz w hw a b ha hb hab
  rcases hz with ⟨x, hx, hz⟩
  rcases hw with ⟨x', hx', hw⟩
  -- Step 1: the witness row `a x + b x'` lies in `X` by convexity.
  refine ⟨a • x + b • x', hX hx hx' ha hb hab, ?_⟩
  intro y
  -- Step 2: convexity of `f(·, y)` on `X` at the two witness rows.
  have hconv := (hf (y : Y) (y : Y).2).2 hx hx' ha hb hab
  have hz_y := hz y
  have hw_y := hw y
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hconv hz_y hw_y ⊢
  -- Step 3: combine the strict witness inequalities, by cases on the weights.
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
  -- Step 4: chain Steps 2 and 3.
  exact hconv.trans_lt hlt

/-- The upper image is coordinatewise upward closed: increasing any coordinates of a
member keeps it in the upper image, with the same witness row. -/
lemma finiteUpperImage_upper {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {z : u → ℝ} (hz : z ∈ finiteUpperImage X f u) {z' : u → ℝ}
    (hzz' : ∀ y : u, z y ≤ z' y) :
    z' ∈ finiteUpperImage X f u := by
  rcases hz with ⟨x, hx, hz⟩
  exact ⟨x, hx, fun y => (hz y).trans_le (hzz' y)⟩

/-- The upper image of a finite column sample is open in the product topology: for a
fixed row `x`, membership is finitely many strict inequalities `f x y < z y`, each an
open condition, and the upper image is the union of these open sets over `x ∈ X`. -/
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

/-- A continuous linear functional `L` on a finite product `ι → ℝ` is determined by its
coordinate coefficients: `L z = Σ_i z i · L(e_i)`, where `e_i` is the `i`-th standard
basis vector. Those coefficients are what we normalize into probabilities. -/
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

/-- If the functional `L` separates the upper image of a finite column sample from the
point `cvec` (`L z < L cvec` for every `z` in the upper image), then no coordinate
coefficient `L(e_y)` of `L` is positive.

**Proof sketch.** Suppose `L(e_y) > 0` for some sampled column `y`. Step 1: take any
point `z` of the (nonempty) upper image and the step size
`t := (L cvec − L z + 1) / L(e_y) ≥ 0`. Step 2: `z + t e_y` still lies in the upper image
by upward closedness. Step 3: by linearity `L(z + t e_y) = L cvec + 1`, contradicting
separation. -/
lemma separating_coordinate_nonpos {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    ∀ y : u, L (Pi.single y (1 : ℝ)) ≤ 0 := by
  classical
  intro y
  by_contra hnot
  have hpos : 0 < L (Pi.single y (1 : ℝ)) := lt_of_not_ge hnot
  -- Step 1: a point of the upper image and a nonnegative step size `t`.
  rcases finiteUpperImage_nonempty (X := X) (Y := Y) (f := f) hX u with ⟨z, hz⟩
  let t := (L cvec - L z + 1) / L (Pi.single y (1 : ℝ))
  have ht_nonneg : 0 ≤ t := by
    have hnum : 0 ≤ L cvec - L z + 1 := by
      have := hsep z hz
      linarith
    exact div_nonneg hnum hpos.le
  -- Step 2: the shifted point stays in the upper image.
  have hz' :
      z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ) ∈ finiteUpperImage X f u := by
    refine finiteUpperImage_upper hz ?_
    intro y'
    by_cases hyy' : y' = y
    · subst hyy'
      simp [ht_nonneg]
    · simp [Pi.single_eq_of_ne hyy']
  -- Step 3: its `L`-value is `L cvec + 1`, contradicting separation.
  have hlt := hsep (z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ)) hz'
  have hcalc : L (z + t • Pi.single (M := fun _ : u => ℝ) y (1 : ℝ)) = L cvec + 1 := by
    simp [t, map_add, map_smul, smul_eq_mul, hpos.ne']
    field_simp [hpos.ne']
    ring
  rw [hcalc] at hlt
  linarith

/-- A functional separating the (nonempty) upper image from a point is nonzero: the zero
functional cannot be strictly smaller on every upper-image point than on `cvec`. -/
lemma separating_functional_ne_zero {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    L ≠ 0 := by
  intro hL
  rcases finiteUpperImage_nonempty (X := X) (Y := Y) (f := f) hX u with ⟨z, hz⟩
  simpa [hL] using hsep z hz

/-- For a functional `L` separating the upper image of a finite column sample from a
point, the negated coordinate coefficients `−L(e_y)` have strictly positive total mass
`Σ_y −L(e_y) > 0`; dividing by this mass turns them into a probability vector.

**Proof sketch.** Step 1: every `−L(e_y)` is nonnegative by
`separating_coordinate_nonpos`. Step 2: some coefficient is nonzero, since otherwise the
coordinate expansion `continuousLinearMap_pi_apply_eq_sum_single` would make `L = 0`,
contradicting `separating_functional_ne_zero`. Step 3: that coefficient is then strictly
negative, so the sum of nonnegative terms with one positive term is positive. -/
lemma separating_weight_sum_pos {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {cvec : u → ℝ} (hX : X.Nonempty) (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L cvec) :
    0 < ∑ y : u, -L (Pi.single y (1 : ℝ)) := by
  classical
  -- Step 1: all negated coefficients are nonnegative.
  have hnonpos := separating_coordinate_nonpos (X := X) (Y := Y) (f := f) hX L hsep
  have hnonneg : ∀ y : u, 0 ≤ -L (Pi.single y (1 : ℝ)) := by
    intro y
    linarith [hnonpos y]
  -- Step 2: some coefficient is nonzero, else `L = 0`.
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
  -- Step 3: that coefficient is strictly negative; the sum is positive.
  rcases hne with ⟨y, hy⟩
  have hpos_y : 0 < -L (Pi.single y (1 : ℝ)) := by
    have hle := hnonpos y
    have hlt : L (Pi.single y (1 : ℝ)) < 0 := lt_of_le_of_ne hle hy
    linarith
  exact Finset.sum_pos' (fun i _ => hnonneg i) ⟨y, Finset.mem_univ y, hpos_y⟩

/-- The algebraic heart of the separation argument: if `L` separates the upper image of
a finite column sample from the constant vector `c` (`L z < L (c, …, c)` for all `z` in
the upper image) and `W = Σ_y −L(e_y) > 0`, then for every row `x ∈ X` the constant `c`
is at most the average payoff `Σ_y (−L(e_y)/W) · f x y` of `x` under the normalized
weights.

**Proof sketch.** It suffices to show `c ≤ average + δ` for every `δ > 0`. Step 1: for a
fixed row `x`, the shifted payoff vector `y ↦ f x y + δ` lies in the upper image, so
separation gives `L(f x · + δ) < L(c, …, c)`. Step 2: expand both sides in coordinates via
`continuousLinearMap_pi_apply_eq_sum_single`, using `Σ_y L(e_y) = −W`. Step 3: multiply
the target inequality by `W > 0` and compare with Step 2's inequality. -/
lemma separating_functional_normalized_le {X Y : Set ℝ} {f : ℝ → ℝ → ℝ} {u : Finset Y}
    {c W : ℝ} (L : (u → ℝ) →L[ℝ] ℝ)
    (hsep : ∀ z ∈ finiteUpperImage X f u, L z < L (fun _ => c))
    (hW : W = ∑ y : u, -L (Pi.single y (1 : ℝ))) (hWpos : 0 < W)
    {x : ℝ} (hxX : x ∈ X) :
    c ≤ ∑ y : u, (-L (Pi.single y (1 : ℝ)) / W) * f x (y : ℝ) := by
  classical
  apply le_of_forall_pos_le_add
  intro δ hδ
  -- Step 1: the shifted payoff vector `f x · + δ` lies in the upper image, so
  -- separation applies to it.
  have hlt : L (fun y : u => f x (y : ℝ) + δ) < L (fun _ => c) :=
    hsep _ ⟨x, hxX, fun y => by simp [hδ]⟩
  -- Step 2: expand both sides of the separation inequality in coordinates.
  have hsum : ∑ y : u, L (Pi.single y (1 : ℝ)) = -W := by
    rw [hW, Finset.sum_neg_distrib, neg_neg]
  have hLz : L (fun y : u => f x (y : ℝ) + δ) =
      ∑ y : u, f x (y : ℝ) * L (Pi.single y (1 : ℝ)) +
        δ * ∑ y : u, L (Pi.single y (1 : ℝ)) := by
    rw [continuousLinearMap_pi_apply_eq_sum_single L, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hLc : L (fun _ : u => c) = c * ∑ y : u, L (Pi.single y (1 : ℝ)) := by
    rw [continuousLinearMap_pi_apply_eq_sum_single L, Finset.mul_sum]
  rw [hLz, hLc, hsum] at hlt
  -- Step 3: clear the denominator `W > 0` and compare.
  have hWne : W ≠ 0 := hWpos.ne'
  have hkey : c * W ≤ (∑ y : u, (-L (Pi.single y (1 : ℝ)) / W) * f x (y : ℝ) + δ) * W := by
    have hterm : ∑ y : u, (-L (Pi.single y (1 : ℝ)) / W) * f x (y : ℝ) * W =
        -(∑ y : u, f x (y : ℝ) * L (Pi.single y (1 : ℝ))) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [show (-L (Pi.single y (1 : ℝ)) / W) * f x (y : ℝ) * W =
          -(f x (y : ℝ) * L (Pi.single y (1 : ℝ))) * (W / W) by ring, div_self hWne, mul_one]
    rw [add_mul, Finset.sum_mul, hterm]
    linarith
  exact le_of_mul_le_mul_right hkey hWpos

/-- The key separation lemma: under `ConvexCompactMinimaxHypotheses`, for every `ε > 0`
and every finite set `u` of column points, there is a row `x ∈ X` whose payoff is at most
`v + ε` on all columns in `u`, where `v = sup_{y ∈ Y} inf_{x ∈ X} f x y` is the lower
value. [CBL06, Thm 7.1]. Deviation: proved by Hahn–Banach separation on the finite column
sample rather than by the source's no-regret argument (see the module docstring).

**Proof sketch.** Let `c := v + ε` and `cvec` the constant vector `c` on `u`.
Step 1 (trivial case): if `cvec` lies in the upper image of `u`, its witness row has
`f x y < c` on every sampled column. Step 2 (Hahn–Banach): otherwise
`geometric_hahn_banach_open_point` separates the open convex upper image from `cvec` by
a functional `L` with `L z < L cvec` on the upper image. Step 3: the normalized negated
coefficients `q y := −L(e_y)/W`, with `W = Σ_y −L(e_y) > 0`, form a mixed column strategy
on `u` (`hWpos`, `hq_nonneg`, `hq_sum`). Step 4 (`hsep_le`): by
`separating_functional_normalized_le`, `c ≤ Σ_y q y · f x y` for every row `x ∈ X`.
Step 5: the `q`-average `ȳ := Σ_y q y · y` lies in `Y` by convexity. Step 6 (Jensen):
concavity in the column variable gives `Σ_y q y · f x y ≤ f x ȳ`, hence `c ≤ f x ȳ` for
all `x ∈ X`. Step 7 (contradiction): `c ≤ inf_x f x ȳ ≤ v`, contradicting `c = v + ε`. -/
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
  -- Step 1 (trivial case): membership of the constant vector gives a row with
  -- `f x y < c` on every sampled column, which is stronger than the sublevel
  -- condition we need.
  · rcases hc with ⟨x, hxX, hxlt⟩
    refine ⟨x, hxX, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro y
    refine Set.mem_iInter.mpr ?_
    intro hyu
    exact ⟨hxX, (hxlt ⟨y, hyu⟩).le⟩
  -- Step 2 (Hahn–Banach): the constant vector is outside the open convex upper
  -- image.  Separation gives a functional `L`; the previous lemmas show that
  -- `-L(e_y)` can be normalized into weights on the sampled columns.
  · obtain ⟨L, hsep⟩ :=
      geometric_hahn_banach_open_point
        (finiteUpperImage_convex (X := X) (Y := Y) (f := f) u h.X_convex h.convex_left)
        (finiteUpperImage_isOpen (X := X) (Y := Y) (f := f) u) hc
    -- Step 3: the normalized coefficients `q` form a mixed column strategy.
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
    -- Step 4: the algebraic heart — separation, expanded in coordinates and
    -- normalized by `W`, bounds `c` by the `q`-average payoff of every row.
    have hsep_le : ∀ x ∈ X, c ≤ ∑ y : u, q y * f x (y : ℝ) := fun x hxX =>
      separating_functional_normalized_le (c := c) L hsep rfl hWpos hxX
    -- Step 5: the weights `q` are a probability distribution on the sampled
    -- columns.  Convexity of `Y` makes their weighted average `ybar` an actual point of
    -- `Y`, and concavity in the column variable gives Jensen's inequality:
    -- average payoff at the sampled columns is at most payoff at `ybar`.
    let ybar : ℝ := ∑ y : u, q y * (y : ℝ)
    have hybar : ybar ∈ Y := by
      simpa [ybar, smul_eq_mul] using
        h.Y_convex.sum_mem (t := Finset.univ) (w := q) (z := fun y : u => (y : ℝ))
          (fun y _ => hq_nonneg y) (by simpa using hq_sum) (fun y _ => (y : Y).2)
    -- Step 6 (Jensen): concavity in the column variable lifts the bound to `ybar`.
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
    -- Step 7 (contradiction): the same column `ybar` satisfies `c ≤ f x ybar`
    -- for every row.
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

/-- The minimax identity from the finite sublevel intersection property: under
`ConvexCompactMinimaxHypotheses`, if for every `ε > 0` and every finite set `u` of column
points some row `x ∈ X` has `f x y ≤ v + ε` for all `y ∈ u` (with `v` the lower value),
then the upper and lower values coincide (`ConvexCompactMinimaxStatement`).
[CBL06, Thm 7.1]. This packages the compactness argument of the source's proof.

**Proof sketch.** By `le_antisymm`. Step 1 (hard direction, `upper ≤ lower`): it suffices
to show `upper ≤ v + ε` for every `ε > 0`. Compactness of `X`
(`exists_forall_le_of_finite_sublevel_intersections`) turns the finite-sample hypothesis
into a single row `x ∈ X` with `f x y ≤ v + ε` for every `y ∈ Y`; then
`sup_y f x y ≤ v + ε` (`hsup_le`) and `upper ≤ sup_y f x y` since the upper value is an
infimum over rows (`hleft_le`). Step 2 (easy direction): `weak_convex_compact_minimax`. -/
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
  -- Step 1: the hard direction, by compactness and letting `ε → 0`.
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
  -- Step 2: the reverse inequality is the standard weak minimax inequality from
  -- the core file.
  · exact weak_convex_compact_minimax h

/-- The convex-compact minimax theorem via the separation route: under
`ConvexCompactMinimaxHypotheses` (nonempty compact convex `X ⊆ ℝ`, nonempty convex
`Y ⊆ ℝ`, bounded `f` continuous and convex in the row variable, concave in the column
variable), the upper value `inf_x sup_y f x y` equals the lower value
`sup_y inf_x f x y`. [CBL06, Thm 7.1]. Deviation: specialized to `ℝ`, and proved by
Hahn–Banach separation on finite column samples plus compactness rather than by the
source's regret-based route (whose last step is isolated, and proved under strengthened
hypotheses, in `ConvexMinimaxNoRegret`); [Kom88] is a different route to a more general
result, and this file does not follow Komiya's argument either. -/
theorem convex_compact_minimax_by_separation {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    ConvexCompactMinimaxStatement X Y f := by
  exact convex_compact_minimax_of_finite_sublevel_intersections h
    (finite_sublevel_intersections_by_separation h)

end OnlineLearning
