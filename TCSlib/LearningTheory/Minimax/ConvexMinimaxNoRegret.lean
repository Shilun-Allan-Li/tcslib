/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/

import TCSlib.LearningTheory.Minimax.ConvexMinimaxCore
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.UniformSpace.HeineCantor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# No-Regret Proof Route for Convex-Compact Minimax (Theorem 7.1)

This file follows the proof of the convex-compact minimax theorem [CBL06, Thm 7.1] as the
source gives it — a finite-row no-regret step followed by a "let the net size go to
zero" compactness step — and isolates the last step as a separate `Prop`, which is
proved here under strengthened hypotheses.

**The isolated step.** The source's last step passes from a finite row sample `u ⊆ X` to
all of `X`: the sampled lower value `sup_y inf_{x ∈ u} f x y` must approximate the full
lower value `sup_y inf_{x ∈ X} f x y` within `ε`, for a single finite `u` that works
*uniformly over all columns `y`*. This step is packaged as the `Prop`
`Theorem71CompactApproximation`. It is not derived here from the theorem's hypotheses
alone (continuity in `x` for each fixed `y`); it is proved under uniform equicontinuity of
`f` in the row variable, uniformly over `y` (`Theorem71UniformEquicontinuity`), or under
joint continuity on a compact `X × Y`. We do not claim the source's argument is wrong.
`convex_compact_minimax_of_theorem71_route` shows the theorem follows from
`Theorem71CompactApproximation` together with the finite no-regret bound, and
`theorem71_compactApproximation_of_uniformEquicontinuity` /
`theorem71_compactApproximation_of_jointContinuous_compact` prove it under the
strengthened hypotheses. The unconditional theorem is proved by a different route in
`TCSlib.LearningTheory.Minimax.ConvexMinimaxSeparation`.

## Main definitions

- `finiteRowSampleLowerValue`, `finiteIndexedRowSampleLowerValue`: the lower value with
  the row player restricted to a finite (finset-indexed or `Fin M`-indexed) sample.
- `Theorem71FiniteNoRegretBound`: the finite-row inequality supplied by no-regret.
- `Theorem71CompactApproximation`: the compact approximation claim in the source's last
  step.
- `Theorem71UniformEquicontinuity`: the extra regularity under which it is proved here.

## Main results

- `convex_compact_minimax_of_theorem71_route`: the minimax equality follows from the
  finite no-regret bound together with compact approximation.
- `convex_compact_minimax_noRegret_jointCompact_normalized`: the minimax equality under
  compact `Y`, joint continuity on `X × Y`, and normalized payoffs, via no-regret plus
  compact approximation.
- `theorem71_finiteNoRegretBound_normalized`: the finite-row no-regret bound — for every
  nonempty finite row sample, the upper value is at most the sampled lower value
  (with `finiteIndexed_column_sample_step` as its finite-column ingredient).
- `theorem71_compactApproximation_of_jointContinuous_compact`: compact approximation of
  the lower value from joint continuity on compact `X × Y`, via finite covers.

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*,
  Cambridge University Press, 2006. Chapter 7 (Theorem 7.1 and its proof).

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

namespace OnlineLearning

/-- The lower value `sup_{y ∈ Y} inf_{x ∈ u} f x y` obtained by restricting the row player
to a finite sample `u ⊆ X`, while the column player still ranges over all of `Y`.
[CBL06, proof of Thm 7.1]. -/
noncomputable def finiteRowSampleLowerValue {X Y : Set ℝ} (f : ℝ → ℝ → ℝ)
    (u : Finset X) : ℝ :=
  ⨆ y : Y, ⨅ x : u, f (x : X) (y : Y)

/-- The finite no-regret bound from the proof of [CBL06, Thm 7.1]: the `Prop` stating
that for every nonempty finite row sample `u ⊆ X`, the upper value
`inf_{x ∈ X} sup_{y ∈ Y} f x y` is at most the sampled lower value
`sup_{y ∈ Y} inf_{x ∈ u} f x y`. This is the part supplied in the source by running
Hedge on the finite row sample. It is stated as a separate `Prop` so the final route can
be assembled cleanly from a finite-game/no-regret ingredient and a compactness
ingredient. -/
def Theorem71FiniteNoRegretBound {X Y : Set ℝ} (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ u : Finset X, u.Nonempty →
    (⨅ x : X, ⨆ y : Y, f x y) ≤
      finiteRowSampleLowerValue (X := X) (Y := Y) f u

/-- The compact approximation claim in the final "let the net size go to zero"
step of the proof of [CBL06, Thm 7.1]: the `Prop` stating that for every `ε > 0` there is
a nonempty finite row sample `u ⊆ X` whose sampled lower value
`sup_{y ∈ Y} inf_{x ∈ u} f x y` is at most the full lower value
`sup_{y ∈ Y} inf_{x ∈ X} f x y` plus `ε`. Deviation: this `Prop` is not derived here from
the theorem's hypotheses alone; it is proved under uniform equicontinuity in the row
variable, uniformly over columns (`theorem71_compactApproximation_of_uniformEquicontinuity`),
or under joint continuity on a compact `X × Y`; see the module docstring. -/
def Theorem71CompactApproximation {X Y : Set ℝ} (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ u : Finset X, u.Nonempty ∧
    finiteRowSampleLowerValue (X := X) (Y := Y) f u ≤
      (⨆ y : Y, ⨅ x : X, f x y) + ε

/-- Uniform equicontinuity of `f` in the row variable, uniformly over all columns: the
`Prop` stating that for every `ε > 0` there is `ρ > 0` such that `|f x y − f x' y| < ε`
whenever `x, x' ∈ X` are within distance `ρ` and `y ∈ Y`. This is the extra regularity,
beyond the hypotheses of [CBL06, Thm 7.1], that makes the finite-cover proof of compact
approximation work directly. -/
def Theorem71UniformEquicontinuity (X Y : Set ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ ρ > 0, ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y,
    dist x x' < ρ → |f x y - f x' y| < ε

/-- The lower value `sup_{y ∈ Y} inf_{i} f (x i) y` of a finite row sample indexed by
`Fin M`, with the column player ranging over all of `Y`. [CBL06, proof of Thm 7.1]. -/
noncomputable def finiteIndexedRowSampleLowerValue {X Y : Set ℝ} {M : ℕ}
    (f : ℝ → ℝ → ℝ) (x : Fin M → X) : ℝ :=
  ⨆ y : Y, ⨅ i : Fin M, f (x i : X) (y : Y)

/-- Assembly of the proof route of [CBL06, Thm 7.1]: under
`ConvexCompactMinimaxHypotheses`, if the finite no-regret bound
(`Theorem71FiniteNoRegretBound`) and compact approximation
(`Theorem71CompactApproximation`) both hold, then the upper and lower values coincide
(`ConvexCompactMinimaxStatement`). The hard direction is the source's ε-argument: for
`ε > 0` choose a finite row sample within `ε` of the full lower value, then apply the
finite no-regret inequality on that sample; the easy direction is
`weak_convex_compact_minimax`. -/
theorem convex_compact_minimax_of_theorem71_route {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f)
    (hfinite : Theorem71FiniteNoRegretBound (X := X) (Y := Y) f)
    (happrox : Theorem71CompactApproximation (X := X) (Y := Y) f) :
    ConvexCompactMinimaxStatement X Y f := by
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  unfold ConvexCompactMinimaxStatement
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    -- Choose a finite row sample close enough to the full lower value, then
    -- use the finite no-regret inequality on that sample.
    rcases happrox ε hε with ⟨u, hu_nonempty, hu_approx⟩
    exact (hfinite u hu_nonempty).trans hu_approx
  · exact weak_convex_compact_minimax h

/-- Compact approximation from a finite cover of `X`: under
`ConvexCompactMinimaxHypotheses`, uniform equicontinuity of `f` in the row variable
uniformly over columns (`Theorem71UniformEquicontinuity`) implies
`Theorem71CompactApproximation`. [CBL06, proof of Thm 7.1 (the finite-net step, with
the missing uniformity hypothesis made explicit)].

**Proof sketch.** Fix `ε > 0` and let `C` be the full lower value. Step 1: uniform
equicontinuity at `ε/2` gives a radius `ρ` that works for all columns. Step 2:
compactness of `X` gives a finite set `u ⊆ X` of centres whose `ρ`-balls cover `X`
(nonempty since `X` is). Step 3: for a fixed column `y`, `inf_x f x y ≤ C`, so there is a
nearly optimal row `x₀ ∈ X` with `f x₀ y < C + ε/2`. Step 4: `x₀` lies within `ρ` of some
centre `x ∈ u`, and equicontinuity transfers the bound: `f x y < C + ε`; hence the
sampled infimum over `u` at `y` is at most `C + ε`, and taking `sup` over `y` gives the
claim. -/
theorem theorem71_compactApproximation_of_uniformEquicontinuity {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (heq : Theorem71UniformEquicontinuity X Y f) :
    Theorem71CompactApproximation (X := X) (Y := Y) f := by
  classical
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  intro ε hε
  let C : ℝ := ⨆ y : Y, ⨅ x : X, f x y
  -- Step 1: uniform equicontinuity gives a single radius that works for all columns.
  obtain ⟨ρ, hρ, hmod⟩ := heq (ε / 2) (by linarith)
  -- Step 2: compactness of `X` then supplies finitely many row points at that radius.
  obtain ⟨u, hu_cover⟩ :=
    h.X_compact.elim_finite_subcover
      (fun x : X => Metric.ball (x : ℝ) ρ)
      (fun _ => Metric.isOpen_ball)
      (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hρ⟩)
  have hu_nonempty : u.Nonempty := by
    rcases h.X_nonempty with ⟨x₀, hx₀⟩
    rcases Set.mem_iUnion.mp (hu_cover hx₀) with ⟨xNear, hxNear⟩
    rcases Set.mem_iUnion.mp hxNear with ⟨hxNear_mem, _⟩
    exact ⟨xNear, hxNear_mem⟩
  refine ⟨u, hu_nonempty, ?_⟩
  unfold finiteRowSampleLowerValue
  apply ciSup_le
  intro y
  -- Step 3: for this fixed column `y`, choose a nearly optimal row point `x₀`.
  have hbddAbove_inf : BddAbove (Set.range fun y : Y => ⨅ x : X, f x y) := by
    rcases h.bounded_above with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro _ ⟨y', rfl⟩
    have hbelow_y : BddBelow (Set.range fun x : X => f x y') := by
      rcases h.bounded_below with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact ha ⟨(x, y'), rfl⟩
    exact (ciInf_le hbelow_y (Classical.choice inferInstance)).trans
      (hb ⟨(Classical.choice inferInstance, y'), rfl⟩)
  have hinf_lt_target : (⨅ x : X, f x y) < C + ε / 2 := by
    have hinf_le_C : (⨅ x : X, f x y) ≤ C := by
      exact le_ciSup hbddAbove_inf y
    linarith
  obtain ⟨x₀, hx₀_lt⟩ := exists_lt_of_ciInf_lt hinf_lt_target
  -- Step 4: the finite cover gives a nearby sampled point, and uniform equicontinuity
  -- transfers the value from `x₀` to that sampled point.
  rcases Set.mem_iUnion.mp (hu_cover x₀.2) with ⟨xNear, hxNear⟩
  rcases Set.mem_iUnion.mp hxNear with ⟨hxNear_mem, hxNear_ball⟩
  let xNearU : u := ⟨xNear, hxNear_mem⟩
  have hdist : dist (xNear : ℝ) (x₀ : ℝ) < ρ := by
    simpa [dist_comm] using hxNear_ball
  have hclose :
      |f (xNear : ℝ) (y : ℝ) - f (x₀ : ℝ) (y : ℝ)| < ε / 2 :=
    hmod (xNear : ℝ) xNear.2 (x₀ : ℝ) x₀.2 (y : ℝ) y.2 hdist
  have hxNear_lt : f (xNear : ℝ) (y : ℝ) < C + ε := by
    rcases abs_lt.mp hclose with ⟨_, hupper⟩
    linarith
  have hbelow_u_y :
      BddBelow (Set.range fun x' : u => f (x' : X) (y : Y)) := by
    rcases h.bounded_below with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rintro _ ⟨x', rfl⟩
    exact ha ⟨((x' : X), y), rfl⟩
  exact (ciInf_le hbelow_u_y xNearU).trans hxNear_lt.le

/-- Joint continuity of `f` on the compact product `X × Y` (with `Y` compact in addition
to `ConvexCompactMinimaxHypotheses`) implies uniform equicontinuity in the row variable
uniformly over columns (`Theorem71UniformEquicontinuity`). By the Heine–Cantor theorem,
`f` is uniformly continuous on the compact set `X × Y`; specializing to pairs that differ
only in the first coordinate gives the claim. [CBL06, proof of Thm 7.1] + Heine–Cantor. -/
theorem theorem71_uniformEquicontinuity_of_jointContinuous_compact {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (hY_compact : IsCompact Y)
    (hjoint : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (X ×ˢ Y)) :
    Theorem71UniformEquicontinuity X Y f := by
  intro ε hε
  -- Heine-Cantor turns joint continuity on the compact product into uniform
  -- continuity.  We then vary only the first coordinate.
  have hXY_compact : IsCompact (X ×ˢ Y) := h.X_compact.prod hY_compact
  have hUC :
      UniformContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (X ×ˢ Y) :=
    hXY_compact.uniformContinuousOn_of_continuous hjoint
  rcases (Metric.uniformContinuousOn_iff.mp hUC) ε hε with ⟨ρ, hρ, hρ_prop⟩
  refine ⟨ρ, hρ, ?_⟩
  intro x hx x' hx' y hy hdist
  have hpair_dist : dist ((x, y) : ℝ × ℝ) ((x', y) : ℝ × ℝ) < ρ := by
    simpa [Prod.dist_eq] using hdist
  have hdist_f :=
    hρ_prop (x, y) ⟨hx, hy⟩ (x', y) ⟨hx', hy⟩ hpair_dist
  simpa [Real.dist_eq] using hdist_f

/-- Compact approximation (`Theorem71CompactApproximation`) under the strengthened
assumptions that `Y` is compact and `f` is jointly continuous on `X × Y`: joint
continuity gives uniform equicontinuity by Heine–Cantor, and the finite-cover argument
does the rest. [CBL06, proof of Thm 7.1] + Heine–Cantor. -/
theorem theorem71_compactApproximation_of_jointContinuous_compact {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (hY_compact : IsCompact Y)
    (hjoint : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (X ×ˢ Y)) :
    Theorem71CompactApproximation (X := X) (Y := Y) f := by
  -- The compact-product continuity assumption is used only to get the uniform
  -- equicontinuity required by the previous theorem.
  exact theorem71_compactApproximation_of_uniformEquicontinuity h
    (theorem71_uniformEquicontinuity_of_jointContinuous_compact h hY_compact hjoint)

/-- A real family with values at most `1` has range bounded above. -/
private lemma bddAbove_of_le_one {ι : Sort*} {g : ι → ℝ} (hg : ∀ i, g i ≤ 1) :
    BddAbove (Set.range g) :=
  ⟨1, by rintro _ ⟨i, rfl⟩; exact hg i⟩

/-- A nonnegative real family has range bounded below. -/
private lemma bddBelow_of_nonneg {ι : Sort*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) :
    BddBelow (Set.range g) :=
  ⟨0, by rintro _ ⟨i, rfl⟩; exact hg i⟩

/-- Infima over a nonempty index of a `[0, 1]`-valued family are bounded above by `1`. -/
private lemma bddAbove_range_iInf_of_unitInterval {ι κ : Type*} [Nonempty ι]
    {g : ι → κ → ℝ} (hg : ∀ i j, 0 ≤ g i j ∧ g i j ≤ 1) :
    BddAbove (Set.range fun j : κ => ⨅ i : ι, g i j) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact (ciInf_le (bddBelow_of_nonneg fun i => (hg i j).1) (Classical.arbitrary ι)).trans
    (hg _ j).2

/-- Suprema over a nonempty index of a `[0, 1]`-valued family are bounded below by `0`. -/
private lemma bddBelow_range_iSup_of_unitInterval {ι κ : Type*} [Nonempty κ]
    {g : ι → κ → ℝ} (hg : ∀ i j, 0 ≤ g i j ∧ g i j ≤ 1) :
    BddBelow (Set.range fun i : ι => ⨆ j : κ, g i j) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (hg i (Classical.arbitrary κ)).1.trans
    (le_ciSup (bddAbove_of_le_one fun j => (hg i j).2) (Classical.arbitrary κ))

/-- The finite-column ingredient of `theorem71_finiteIndexedNoRegretBound_normalized`:
under `ConvexCompactMinimaxHypotheses` with `0 ≤ f ≤ 1` on `X × Y`, for a row sample
`x : Fin M → X` with `M ≥ 2`, every `ε > 0`, and every finite column sample `v ⊆ Y`,
there is a row `x̄ ∈ X` with `f x̄ y ≤ K + ε` for every `y ∈ v`, where
`K = sup_{y ∈ Y} inf_i f (x i) y` is the indexed sampled lower value.
[CBL06, proof of Thm 7.1 (finite ε-net step)].

**Proof sketch.** Let `c := K + ε`. Step 0: if `v` is empty, any point of `X` works.
Otherwise index `v` by `Fin v.card`. Step 1: build the finite zero-sum game `G` on the
row sample and the column sample with payoff `1 − f (x i) (y j)`, which lies in `[0, 1]`.
Step 2: `finite_minimax_value` gives `lower(G) = upper(G)`, and `1 − K ≤ upper(G)`: for
any column mixed strategy `q`, the mixture `ȳ := Σ_j q j · y j` lies in `Y` by convexity,
`inf_i f (x i) ȳ ≤ K` by definition of `K`, and for a minimizing row `i₀` concavity in
the column variable (Jensen) gives `Σ_j q j · f (x i₀) (y j) ≤ f (x i₀) ȳ ≤ K`, i.e. the
payoff of `i₀` against `q` is at least `1 − K`. Hence `1 − c < lower(G)`. Step 3: pick a
row mixed strategy `p` whose worst-case sampled payoff exceeds `1 − c`, and let
`x̄ := Σ_i p i · x i ∈ X` by convexity of `X`. Step 4: for each `y ∈ v` the payoff of `p`
against `y` is `1 − Σ_i p i · f (x i) y > 1 − c`, and convexity of `f` in the row variable
(Jensen) gives `f x̄ y ≤ Σ_i p i · f (x i) y < c`. -/
theorem finiteIndexed_column_sample_step {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f)
    (h01 : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ f x y ∧ f x y ≤ 1)
    {M : ℕ} [NeZero M] (hM : 1 < M) (x : Fin M → X) {ε : ℝ} (hε : 0 < ε)
    (v : Finset Y) :
    (X ∩ ⋂ y ∈ v, minimaxSublevel X f (y : ℝ)
      (finiteIndexedRowSampleLowerValue (X := X) (Y := Y) f x + ε)).Nonempty := by
  classical
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  have h01' : ∀ (x' : X) (y : Y), 0 ≤ f x' y ∧ f x' y ≤ 1 := fun x' y => h01 x' x'.2 y y.2
  let K : ℝ := finiteIndexedRowSampleLowerValue (X := X) (Y := Y) f x
  let c : ℝ := K + ε
  show (X ∩ ⋂ y ∈ v, minimaxSublevel X f (y : ℝ) c).Nonempty
  by_cases hv : v.Nonempty
  · let e : v ≃ Fin v.card := v.equivFin
    let y : Fin v.card → Y := fun j => (e.symm j : v)
    have hv_card_pos : 0 < v.card := Finset.card_pos.mpr hv
    haveI : NeZero v.card := ⟨Nat.pos_iff_ne_zero.mp hv_card_pos⟩
    -- Step 1: the finite game uses payoff `1 - f` so that the finite minimax theorem
    -- can be applied to normalized payoffs in `[0, 1]`.
    let G : ZeroSumGame M v.card := {
      payoff i j := 1 - f (x i : X) (y j : Y)
      payoff_nonneg i j := by
        exact sub_nonneg.mpr ((h01 (x i : X) (x i).2 (y j : Y) (y j).2).2)
      payoff_le_one i j := by
        have hnonneg := (h01 (x i : X) (x i).2 (y j : Y) (y j).2).1
        linarith
    }
    -- Step 2: finite minimax, and Jensen at `ybar` bounds the upper value.
    have hvalue := finite_minimax_value G hM
    have hupper_ge : 1 - K ≤ finiteUpperValue G := by
      unfold finiteUpperValue
      apply le_ciInf
      intro q
      -- A mixed column strategy gives a convex combination `ybar` in `Y`.
      -- Concavity in the column variable compares the sampled average to
      -- the value at `ybar`.
      let ybar : ℝ := ∑ j : Fin v.card, q.weights j * (y j : ℝ)
      have hybar : ybar ∈ Y := by
        simpa [ybar, smul_eq_mul] using
          h.Y_convex.sum_mem (t := Finset.univ) (w := q.weights)
            (z := fun j : Fin v.card => (y j : ℝ))
            (fun j _ => q.nonneg j) (by simpa using q.sum_one) (fun j _ => (y j).2)
      have hK_bddAbove :
          BddAbove (Set.range fun y' : Y => ⨅ i : Fin M, f (x i : X) (y' : Y)) :=
        bddAbove_range_iInf_of_unitInterval fun i y' => h01' (x i) y'
      have hinf_ybar_le_K :
          (⨅ i : Fin M, f (x i : X) ybar) ≤ K := by
        exact le_ciSup hK_bddAbove ⟨ybar, hybar⟩
      have hbelow_ybar : BddBelow (Set.range fun i : Fin M => f (x i : X) ybar) :=
        bddBelow_of_nonneg fun i => (h01 (x i : X) (x i).2 ybar hybar).1
      obtain ⟨i₀, hi₀⟩ := Finite.exists_min (fun i : Fin M => f (x i : X) ybar)
      have hi₀_eq : f (x i₀ : X) ybar = ⨅ i : Fin M, f (x i : X) ybar := by
        apply le_antisymm
        · exact le_ciInf hi₀
        · exact ciInf_le hbelow_ybar i₀
      have havg_le : ∑ j : Fin v.card, q.weights j * f (x i₀ : X) (y j : Y)
          ≤ f (x i₀ : X) ybar := by
        simpa [ybar, smul_eq_mul] using
          (h.concave_right (x i₀ : X) (x i₀).2).le_map_sum
            (t := Finset.univ) (w := q.weights)
            (p := fun j : Fin v.card => (y j : ℝ))
            (fun j _ => q.nonneg j) (by simpa using q.sum_one) (fun j _ => (y j).2)
      have hpure_ge : 1 - K ≤ pureVsPayoff G i₀ q := by
        have hsum_payoff :
            pureVsPayoff G i₀ q =
              1 - ∑ j : Fin v.card, q.weights j * f (x i₀ : X) (y j : Y) := by
          calc
            pureVsPayoff G i₀ q
                = ∑ j : Fin v.card,
                    (q.weights j - q.weights j * f (x i₀ : X) (y j : Y)) := by
                  change (∑ j : Fin v.card,
                      (1 - f (x i₀ : X) (y j : Y)) * q.weights j) =
                    ∑ j : Fin v.card,
                      (q.weights j - q.weights j * f (x i₀ : X) (y j : Y))
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
            _ = (∑ j : Fin v.card, q.weights j) -
                  ∑ j : Fin v.card, q.weights j * f (x i₀ : X) (y j : Y) := by
                  rw [Finset.sum_sub_distrib]
            _ = 1 - ∑ j : Fin v.card, q.weights j * f (x i₀ : X) (y j : Y) := by
                  rw [q.sum_one]
        rw [hsum_payoff]
        have hi_le_K : f (x i₀ : X) ybar ≤ K := by
          rw [hi₀_eq]
          exact hinf_ybar_le_K
        linarith
      have hbdd_sup : BddAbove (Set.range fun i : Fin M => pureVsPayoff G i q) :=
        bddAbove_of_le_one fun i => pureVsPayoff_le_one G i q
      exact hpure_ge.trans (le_ciSup hbdd_sup i₀)
    -- By the finite minimax theorem the same bound holds for the lower value.
    have hlower_ge : 1 - K ≤ finiteLowerValue G := by
      rw [hvalue]
      exact hupper_ge
    have hlt_lower : 1 - c < finiteLowerValue G := by
      dsimp [c]
      linarith
    -- Step 3: pick a row mixed strategy whose sampled lower payoff is above
    -- `1 - c`.  Its convex combination `xbar` will satisfy the finite sublevel
    -- constraints.
    obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hlt_lower
    let xbar : ℝ := ∑ i : Fin M, p.weights i * (x i : ℝ)
    have hxbar : xbar ∈ X := by
      simpa [xbar, smul_eq_mul] using
        h.X_convex.sum_mem (t := Finset.univ) (w := p.weights)
          (z := fun i : Fin M => (x i : ℝ))
          (fun i _ => p.nonneg i) (by simpa using p.sum_one) (fun i _ => (x i).2)
    refine ⟨xbar, hxbar, ?_⟩
    refine Set.mem_iInter.mpr ?_
    intro yv
    refine Set.mem_iInter.mpr ?_
    intro hyv
    let ySub : v := ⟨yv, hyv⟩
    let j : Fin v.card := e ySub
    have hy_eq : (y j : Y) = ySub := by
      dsimp [y, j]
      simp
    have hy_eq_real : (y j : ℝ) = (yv : ℝ) := by
      exact congrArg Subtype.val hy_eq
    have hbelow_payoff :
        BddBelow (Set.range fun j : Fin v.card => payoffVsPure G p j) :=
      bddBelow_of_nonneg fun j' => payoffVsPure_nonneg G p j'
    have hpj : 1 - c < payoffVsPure G p j := by
      exact hp.trans_le (ciInf_le hbelow_payoff j)
    -- Step 4: convexity in the row variable at `xbar`.
    have hconv :
        f xbar (yv : ℝ) ≤
          ∑ i : Fin M, p.weights i * f (x i : X) (yv : ℝ) := by
      have hfconv := h.convex_left (yv : ℝ) yv.2
      simpa [xbar, smul_eq_mul] using
        hfconv.map_sum_le (t := Finset.univ) (w := p.weights)
          (p := fun i : Fin M => (x i : ℝ))
          (fun i _ => p.nonneg i) (by simpa using p.sum_one) (fun i _ => (x i).2)
    have hpayoff_eq :
        payoffVsPure G p j =
          1 - ∑ i : Fin M, p.weights i * f (x i : X) (yv : ℝ) := by
      calc
        payoffVsPure G p j
            = ∑ i : Fin M, (p.weights i - p.weights i * f (x i : X) (yv : ℝ)) := by
              change (∑ i : Fin M,
                  p.weights i * (1 - f (x i : X) (y j : Y))) =
                ∑ i : Fin M, (p.weights i - p.weights i * f (x i : X) (yv : ℝ))
              rw [hy_eq_real]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = (∑ i : Fin M, p.weights i) -
              ∑ i : Fin M, p.weights i * f (x i : X) (yv : ℝ) := by
              rw [Finset.sum_sub_distrib]
        _ = 1 - ∑ i : Fin M, p.weights i * f (x i : X) (yv : ℝ) := by
              rw [p.sum_one]
    have hsum_lt :
        ∑ i : Fin M, p.weights i * f (x i : X) (yv : ℝ) < c := by
      linarith
    exact ⟨hxbar, hconv.trans hsum_lt.le⟩
  · rcases h.X_nonempty with ⟨x₀, hx₀⟩
    -- Step 0: if the finite column sample is empty, any point of `X` satisfies all
    -- of the requested constraints.
    refine ⟨x₀, hx₀, ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hv]

/-- The finite-row no-regret bound of the proof of [CBL06, Thm 7.1], for a row sample
indexed by `Fin M`: under `ConvexCompactMinimaxHypotheses` with the normalization
`0 ≤ f ≤ 1` on `X × Y` and `M ≥ 2`, the upper value `inf_{x ∈ X} sup_{y ∈ Y} f x y` is
at most the sampled lower value `sup_{y ∈ Y} inf_i f (x i) y`. Deviation: the source
obtains this by running Hedge on the row sample against all of `Y`; here the finite
matrix-game minimax theorem (itself proved via Hedge) is applied on each finite column
subset, and compactness of `X` passes to all columns. The hypotheses `0 ≤ f ≤ 1` and
`1 < M` are inherited from `finite_minimax_value`.

**Proof sketch.** Fix `ε > 0`, let `K` be the sampled lower value and `c := K + ε`.
Step 1 (`hfin`): by `finiteIndexed_column_sample_step`, every finite column sample admits
a point of `X` satisfying the sampled sublevel constraints at level `c`. Step 2:
compactness of `X` (`exists_forall_le_of_finite_sublevel_intersections`) gives one row
`x₀ ∈ X` with `f x₀ y ≤ c` for every `y ∈ Y`. Step 3 (`hleft_le`): the upper value is at
most `sup_y f x₀ y`, since it is an infimum over rows. Step 4 (`hsup_le`):
`sup_y f x₀ y ≤ c`. Chain and let `ε → 0`. -/
theorem theorem71_finiteIndexedNoRegretBound_normalized {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (h01 : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ f x y ∧ f x y ≤ 1)
    {M : ℕ} [NeZero M] (hM : 1 < M) (x : Fin M → X) :
    (⨅ x' : X, ⨆ y : Y, f x' y) ≤
      finiteIndexedRowSampleLowerValue (X := X) (Y := Y) f x := by
  classical
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  apply le_of_forall_pos_le_add
  intro ε hε
  let K : ℝ := finiteIndexedRowSampleLowerValue (X := X) (Y := Y) f x
  let c : ℝ := K + ε
  -- Step 1: every finite column sample admits a common point of `X` satisfying
  -- the sampled sublevel constraints at level `c` (finite minimax on `1 - f`).
  have hfin :
      ∀ v : Finset Y,
        (X ∩ ⋂ y ∈ v, minimaxSublevel X f (y : ℝ) c).Nonempty :=
    fun v => finiteIndexed_column_sample_step h h01 hM x hε v
  -- Step 2: compactness of `X` gives one row satisfying all column constraints.
  obtain ⟨x₀, hx₀, hx₀_le⟩ :=
    exists_forall_le_of_finite_sublevel_intersections h c hfin
  let xX : X := ⟨x₀, hx₀⟩
  -- Step 3: the left-hand value is at most `sup_y f x₀ y`.
  have hleft_le : (⨅ x' : X, ⨆ y : Y, f x' y) ≤ ⨆ y : Y, f xX y :=
    ciInf_le (bddBelow_range_iSup_of_unitInterval fun (x' : X) (y : Y) => h01 x' x'.2 y y.2) xX
  -- Step 4: the point obtained by compactness bounds `sup_y f x₀ y` by `K + ε`.
  have hsup_le : (⨆ y : Y, f xX y) ≤ c :=
    ciSup_le fun y => hx₀_le y
  dsimp [c, K] at hsup_le ⊢
  exact hleft_le.trans hsup_le

/-- The finite-row no-regret bound of the proof of [CBL06, Thm 7.1], in finset form: under
`ConvexCompactMinimaxHypotheses` with the normalization `0 ≤ f ≤ 1` on `X × Y`,
`Theorem71FiniteNoRegretBound` holds, i.e. for every nonempty finite row sample `u ⊆ X`
the upper value is at most the sampled lower value `sup_{y ∈ Y} inf_{x ∈ u} f x y`.
Deviation: normalized payoffs, inherited from `finite_minimax_value`.

**Proof sketch.** Step 1 (at least two rows): re-index `u` by `Fin u.card` via
`Finset.equivFin`, apply `theorem71_finiteIndexedNoRegretBound_normalized`, and compare
the indexed infimum with the finset infimum for each column (they agree; the code proves
`inf_i ≤ inf_{u}` and then takes `sup` over columns). Step 2 (singleton): a nonempty
finset of cardinality at most one is `{x₀}`; the upper value is at most `sup_y f x₀ y`,
and the infimum over the singleton at each `y` is exactly `f x₀ y`. -/
theorem theorem71_finiteNoRegretBound_normalized {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f)
    (h01 : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ f x y ∧ f x y ≤ 1) :
    Theorem71FiniteNoRegretBound (X := X) (Y := Y) f := by
  classical
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  have h01' : ∀ (x : X) (y : Y), 0 ≤ f x y ∧ f x y ≤ 1 := fun x y => h01 x x.2 y y.2
  intro u hu
  haveI : Nonempty u := ⟨⟨hu.choose, hu.choose_spec⟩⟩
  by_cases hu_card : 1 < u.card
  · haveI : NeZero u.card := ⟨Nat.pos_iff_ne_zero.mp (lt_trans Nat.zero_lt_one hu_card)⟩
    -- Step 1 (at least two rows): re-index the finite set `u` by `Fin u.card`,
    -- apply the indexed theorem, then compare the indexed infimum with the
    -- original finset infimum.
    let e : u ≃ Fin u.card := u.equivFin
    let x : Fin u.card → X := fun i => (e.symm i : u)
    have hidx :=
      theorem71_finiteIndexedNoRegretBound_normalized h h01 hu_card x
    refine hidx.trans ?_
    unfold finiteIndexedRowSampleLowerValue finiteRowSampleLowerValue
    apply ciSup_le
    intro y
    have hidx_le_u : (⨅ i : Fin u.card, f (x i : X) (y : Y)) ≤
        ⨅ x' : u, f (x' : X) (y : Y) := by
      apply le_ciInf
      intro xu
      have hxeq : x (e xu) = (xu : X) := by
        dsimp [x]
        simp
      rw [← hxeq]
      exact ciInf_le (bddBelow_of_nonneg fun i => (h01' (x i) y).1) (e xu)
    have habove_u :
        BddAbove (Set.range fun y' : Y => ⨅ x' : u, f (x' : X) (y' : Y)) :=
      bddAbove_range_iInf_of_unitInterval fun x' y' => h01' x' y'
    exact hidx_le_u.trans (le_ciSup habove_u y)
  · have hu_card_le : u.card ≤ 1 := Nat.le_of_not_gt hu_card
    rcases hu with ⟨x₀, hx₀⟩
    -- Step 2 (singleton): a nonempty finset of cardinality at most one is a
    -- singleton, so this case reduces directly to comparing with that one row.
    have hu_single : u = {x₀} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hx₀, ?_⟩
      intro x hx
      exact (Finset.card_le_one.mp hu_card_le) x hx x₀ hx₀
    subst hu_single
    unfold finiteRowSampleLowerValue
    have hleft_le : (⨅ x' : X, ⨆ y : Y, f x' y) ≤ ⨆ y : Y, f x₀ y :=
      ciInf_le (bddBelow_range_iSup_of_unitInterval h01') x₀
    refine hleft_le.trans ?_
    apply ciSup_le
    intro y
    let xu : ({x₀} : Finset X) := ⟨x₀, by simp⟩
    have hinf_eq : (⨅ x' : ({x₀} : Finset X), f (x' : X) (y : Y)) = f x₀ y := by
      apply le_antisymm
      · exact ciInf_le (bddBelow_of_nonneg fun x' : ({x₀} : Finset X) => (h01' x' y).1) xu
      · apply le_ciInf
        intro x'
        have hx' : (x' : X) = x₀ := Finset.mem_singleton.mp x'.2
        rw [hx']
    rw [← hinf_eq]
    have habove_single :
        BddAbove
          (Set.range fun y' : Y => ⨅ x' : ({x₀} : Finset X), f (x' : X) (y' : Y)) :=
      bddAbove_range_iInf_of_unitInterval fun x' y' => h01' x' y'
    exact le_ciSup habove_single y

/-- The convex-compact minimax theorem by the no-regret route, under strengthened
hypotheses: if in addition to `ConvexCompactMinimaxHypotheses` the column set `Y` is
compact, `f` is jointly continuous on `X × Y`, and `0 ≤ f ≤ 1` on `X × Y`, then the
upper and lower values coincide (`ConvexCompactMinimaxStatement`). [CBL06, Thm 7.1].
Deviation: strengthened hypotheses (compact `Y`, joint continuity, normalized payoffs) —
compact `Y` and joint continuity supply the uniform equicontinuity under which the
source's last step (`Theorem71CompactApproximation`) is proved here, and normalization is
inherited from `finite_minimax_value`. The finite-row
inequality is supplied by `theorem71_finiteNoRegretBound_normalized` and compact
approximation by `theorem71_compactApproximation_of_jointContinuous_compact`, assembled
by `convex_compact_minimax_of_theorem71_route`; this variant does not use the separation
module. -/
theorem convex_compact_minimax_noRegret_jointCompact_normalized {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (hY_compact : IsCompact Y)
    (hjoint : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (X ×ˢ Y))
    (h01 : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ f x y ∧ f x y ≤ 1) :
    ConvexCompactMinimaxStatement X Y f := by
  -- Combine the normalized finite no-regret ingredient with the compact
  -- approximation theorem obtained from joint continuity on compact `X × Y`.
  exact convex_compact_minimax_of_theorem71_route h
    (theorem71_finiteNoRegretBound_normalized h h01)
    (theorem71_compactApproximation_of_jointContinuous_compact h hY_compact hjoint)

end OnlineLearning
