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

open Real Finset BigOperators

namespace OnlineLearning

/-!
# No-Regret Proof Route for Convex-Compact Minimax (Theorem 7.1)

## Main results

- `convex_compact_minimax_noRegret_jointCompact_normalized`: minimax equality under compact Y, joint continuity on X×Y, and normalized payoffs, via no-regret plus compact approximation
- `theorem71_finiteNoRegretBound_normalized`: finite row no-regret bound: for every nonempty finite row sample, the minimax upper value is bounded by the finite sampled lower value
- `theorem71_compactApproximation_of_jointContinuous_compact`: compact approximation of the lower value from joint continuity on compact X×Y via finite covers

## References

- Original formalization by Karim Abdel Sadek, Mark Bedaywi
-/

/-- The lower value obtained by restricting the row player to a finite sample
`u ⊆ X`, while the column player still ranges over all of `Y`. -/
noncomputable def finiteRowSampleLowerValue {X Y : Set ℝ} (f : ℝ → ℝ → ℝ)
    (u : Finset X) : ℝ :=
  ⨆ y : Y, ⨅ x : u, f (x : X) (y : Y)

/-- The finite no-regret claim appearing in the proof of Theorem 7.1.  This is
the part supplied informally by running Hedge on the finite row sample.

We state it as a separate `Prop` so the final route can be assembled cleanly
from a finite-game/no-regret ingredient and a compactness ingredient. -/
def Theorem71FiniteNoRegretBound {X Y : Set ℝ} (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ u : Finset X, u.Nonempty →
    (⨅ x : X, ⨆ y : Y, f x y) ≤
      finiteRowSampleLowerValue (X := X) (Y := Y) f u

/-- The compact approximation claim hidden in the final "let the net size go to
zero" step of the textbook proof. -/
def Theorem71CompactApproximation {X Y : Set ℝ} (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ u : Finset X, u.Nonempty ∧
    finiteRowSampleLowerValue (X := X) (Y := Y) f u ≤
      (⨆ y : Y, ⨅ x : X, f x y) + ε

/-- Uniform equicontinuity in the row variable, uniformly over all columns.
This is the extra regularity that makes the finite-cover proof of compact
approximation work directly. -/
def Theorem71UniformEquicontinuity (X Y : Set ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ ρ > 0, ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y,
    dist x x' < ρ → |f x y - f x' y| < ε

/-- The lower value of a finite indexed row sample. -/
noncomputable def finiteIndexedRowSampleLowerValue {X Y : Set ℝ} {M : ℕ}
    (f : ℝ → ℝ → ℝ) (x : Fin M → X) : ℝ :=
  ⨆ y : Y, ⨅ i : Fin M, f (x i : X) (y : Y)

/-- Assembly of the Cesa-Bianchi--Lugosi Theorem 7.1 proof route.

Given the finite no-regret bound and the compact finite-approximation property,
the minimax equality follows by the same epsilon argument as in the markdown
proof. -/
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

/-- Compact approximation from a finite cover of `X`, assuming uniform
equicontinuity in `x` uniformly over `y`. -/
theorem theorem71_compactApproximation_of_uniformEquicontinuity {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (heq : Theorem71UniformEquicontinuity X Y f) :
    Theorem71CompactApproximation (X := X) (Y := Y) f := by
  classical
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  intro ε hε
  let C : ℝ := ⨆ y : Y, ⨅ x : X, f x y
  -- Uniform equicontinuity gives a single radius that works for all columns.
  -- Compactness of `X` then supplies finitely many row points at that radius.
  obtain ⟨ρ, hρ, hmod⟩ := heq (ε / 2) (by linarith)
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
  -- For this fixed column `y`, choose a nearly optimal row point `x₀`.
  -- The finite cover gives a nearby sampled point, and uniform equicontinuity
  -- transfers the value from `x₀` to that sampled point.
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

/-- Joint continuity on compact `X × Y` implies the uniform equicontinuity in
the row variable needed by the finite-cover compact approximation proof. -/
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

/-- Compact approximation from the strengthened assumptions: `Y` compact and
`f` jointly continuous on `X × Y`. -/
theorem theorem71_compactApproximation_of_jointContinuous_compact {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f)
    (hY_compact : IsCompact Y)
    (hjoint : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (X ×ˢ Y)) :
    Theorem71CompactApproximation (X := X) (Y := Y) f := by
  -- The compact-product continuity assumption is used only to get the uniform
  -- equicontinuity required by the previous theorem.
  exact theorem71_compactApproximation_of_uniformEquicontinuity h
    (theorem71_uniformEquicontinuity_of_jointContinuous_compact h hY_compact hjoint)

/-- Finite-indexed, normalized finite-row part of the Theorem 7.1 proof.

This proves the core finite-row/infinite-column minimax inequality for a row
sample indexed by `Fin M`, under the normalization `0 ≤ f ≤ 1`.  The proof uses
the finite matrix-game minimax theorem, hence the no-regret development upstream,
on each finite column subset, then compactness of `X` to pass to all columns. -/
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
  -- It is enough to show every finite family of sublevel constraints has a
  -- common point in `X`; compactness will then give a point satisfying all
  -- column constraints at once.
  -- For each finite column sample, build a finite matrix game with payoff
  -- `1 - f`.  Finite minimax gives a row mixture whose convex combination
  -- satisfies the sampled sublevel constraints.
  have hfin :
      ∀ v : Finset Y,
        (X ∩ ⋂ y ∈ v, minimaxSublevel X f (y : ℝ) c).Nonempty := by
    intro v
    by_cases hv : v.Nonempty
    · let e : v ≃ Fin v.card := v.equivFin
      let y : Fin v.card → Y := fun j => (e.symm j : v)
      have hv_card_pos : 0 < v.card := Finset.card_pos.mpr hv
      haveI : NeZero v.card := ⟨Nat.pos_iff_ne_zero.mp hv_card_pos⟩
      -- The finite game uses payoff `1 - f` so that the finite minimax theorem
      -- can be applied to normalized payoffs in `[0, 1]`.
      let G : ZeroSumGame M v.card := {
        payoff i j := 1 - f (x i : X) (y j : Y)
        payoff_nonneg i j := by
          exact sub_nonneg.mpr ((h01 (x i : X) (x i).2 (y j : Y) (y j).2).2)
        payoff_le_one i j := by
          have hnonneg := (h01 (x i : X) (x i).2 (y j : Y) (y j).2).1
          linarith
      }
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
            BddAbove (Set.range fun y' : Y => ⨅ i : Fin M, f (x i : X) (y' : Y)) := by
          refine ⟨1, ?_⟩
          rintro _ ⟨y', rfl⟩
          have hbelow : BddBelow (Set.range fun i : Fin M => f (x i : X) (y' : Y)) := by
            refine ⟨0, ?_⟩
            rintro _ ⟨i, rfl⟩
            exact (h01 (x i : X) (x i).2 (y' : Y) (y' : Y).2).1
          exact (ciInf_le hbelow (Classical.choice inferInstance)).trans
            ((h01 (x (Classical.choice inferInstance) : X)
              (x (Classical.choice inferInstance)).2 (y' : Y) (y' : Y).2).2)
        have hinf_ybar_le_K :
            (⨅ i : Fin M, f (x i : X) ybar) ≤ K := by
          exact le_ciSup hK_bddAbove ⟨ybar, hybar⟩
        have hbelow_ybar : BddBelow (Set.range fun i : Fin M => f (x i : X) ybar) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨i, rfl⟩
          exact (h01 (x i : X) (x i).2 ybar hybar).1
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
        have hbdd_sup : BddAbove (Set.range fun i : Fin M => pureVsPayoff G i q) := by
          refine ⟨1, ?_⟩
          rintro _ ⟨i, rfl⟩
          exact pureVsPayoff_le_one G i q
        exact hpure_ge.trans (le_ciSup hbdd_sup i₀)
      have hlower_ge : 1 - K ≤ finiteLowerValue G := by
        rw [hvalue]
        exact hupper_ge
      have hlt_lower : 1 - c < finiteLowerValue G := by
        dsimp [c]
        linarith
      -- Pick a row mixed strategy whose sampled lower payoff is above `1 - c`.
      -- Its convex combination `xbar` will satisfy the finite sublevel
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
          BddBelow (Set.range fun j : Fin v.card => payoffVsPure G p j) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨j', rfl⟩
        exact payoffVsPure_nonneg G p j'
      have hpj : 1 - c < payoffVsPure G p j := by
        exact hp.trans_le (ciInf_le hbelow_payoff j)
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
      -- If the finite column sample is empty, any point of `X` satisfies all
      -- of the requested constraints.
      refine ⟨x₀, hx₀, ?_⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp hv]
  obtain ⟨x₀, hx₀, hx₀_le⟩ :=
    exists_forall_le_of_finite_sublevel_intersections h c hfin
  let xX : X := ⟨x₀, hx₀⟩
  -- The point obtained by compactness bounds `sup_y f x₀ y` by `K + ε`, which
  -- is enough for the desired left-hand value bound.
  have hleft_le : (⨅ x' : X, ⨆ y : Y, f x' y) ≤ ⨆ y : Y, f xX y := by
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
  have hsup_le : (⨆ y : Y, f xX y) ≤ c := by
    exact ciSup_le fun y => hx₀_le y
  dsimp [c, K] at hsup_le ⊢
  exact hleft_le.trans hsup_le

/-- Finset version of the normalized finite-row Theorem 7.1 bound.

This removes the artificial `Fin M` indexing from
`theorem71_finiteIndexedNoRegretBound_normalized`.  The singleton case is
handled separately because the finite minimax theorem above assumes at least
two row actions. -/
theorem theorem71_finiteNoRegretBound_normalized {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f)
    (h01 : ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ f x y ∧ f x y ≤ 1) :
    Theorem71FiniteNoRegretBound (X := X) (Y := Y) f := by
  classical
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  intro u hu
  by_cases hu_card : 1 < u.card
  · haveI : NeZero u.card := ⟨Nat.pos_iff_ne_zero.mp (lt_trans Nat.zero_lt_one hu_card)⟩
    -- Re-index the finite set `u` by `Fin u.card`, apply the indexed theorem,
    -- then compare the indexed infimum with the original finset infimum.
    let e : u ≃ Fin u.card := u.equivFin
    let x : Fin u.card → X := fun i => (e.symm i : u)
    have hidx :=
      theorem71_finiteIndexedNoRegretBound_normalized h h01 hu_card x
    refine hidx.trans ?_
    unfold finiteIndexedRowSampleLowerValue finiteRowSampleLowerValue
    apply ciSup_le
    intro y
    have hbelow_idx :
        BddBelow (Set.range fun i : Fin u.card => f (x i : X) (y : Y)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨i, rfl⟩
      exact (h01 (x i : X) (x i).2 (y : Y) (y : Y).2).1
    have hidx_le_u : (⨅ i : Fin u.card, f (x i : X) (y : Y)) ≤
        ⨅ x' : u, f (x' : X) (y : Y) := by
      haveI : Nonempty u := by
        rcases hu with ⟨x₀, hx₀⟩
        exact ⟨⟨x₀, hx₀⟩⟩
      apply le_ciInf
      intro xu
      have hxeq : x (e xu) = (xu : X) := by
        dsimp [x]
        simp
      rw [← hxeq]
      exact ciInf_le hbelow_idx (e xu)
    have habove_u :
        BddAbove (Set.range fun y' : Y => ⨅ x' : u, f (x' : X) (y' : Y)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨y', rfl⟩
      haveI : Nonempty u := by
        rcases hu with ⟨x₀, hx₀⟩
        exact ⟨⟨x₀, hx₀⟩⟩
      let xu : u := Classical.choice ‹Nonempty u›
      have hbelow_u_y' : BddBelow (Set.range fun x' : u => f (x' : X) (y' : Y)) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨x', rfl⟩
        exact (h01 (x' : X) (x' : X).2 (y' : Y) (y' : Y).2).1
      exact (ciInf_le hbelow_u_y' xu).trans
        ((h01 (xu : X) (xu : X).2 (y' : Y) (y' : Y).2).2)
    exact hidx_le_u.trans (le_ciSup habove_u y)
  · have hu_card_le : u.card ≤ 1 := Nat.le_of_not_gt hu_card
    rcases hu with ⟨x₀, hx₀⟩
    -- A nonempty finset of cardinality at most one is a singleton, so this
    -- case reduces directly to comparing with that one row point.
    have hu_single : u = {x₀} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hx₀, ?_⟩
      intro x hx
      exact (Finset.card_le_one.mp hu_card_le) x hx x₀ hx₀
    subst hu_single
    unfold finiteRowSampleLowerValue
    have hleft_le : (⨅ x' : X, ⨆ y : Y, f x' y) ≤ ⨆ y : Y, f x₀ y := by
      have hbdd : BddBelow (Set.range fun x' : X => ⨆ y : Y, f x' y) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨x', rfl⟩
        let y₀ : Y := Classical.choice ‹Nonempty Y›
        have habove : BddAbove (Set.range fun y : Y => f x' y) := by
          refine ⟨1, ?_⟩
          rintro _ ⟨y, rfl⟩
          exact (h01 (x' : X) (x' : X).2 (y : Y) (y : Y).2).2
        exact (h01 (x' : X) (x' : X).2 (y₀ : Y) (y₀ : Y).2).1.trans
          (le_ciSup habove y₀)
      exact ciInf_le hbdd x₀
    refine hleft_le.trans ?_
    apply ciSup_le
    intro y
    have hbelow_single :
        BddBelow (Set.range fun x' : ({x₀} : Finset X) => f (x' : X) (y : Y)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨x', rfl⟩
      exact (h01 (x' : X) (x' : X).2 (y : Y) (y : Y).2).1
    let xu : ({x₀} : Finset X) := ⟨x₀, by simp⟩
    have hinf_eq : (⨅ x' : ({x₀} : Finset X), f (x' : X) (y : Y)) = f x₀ y := by
      apply le_antisymm
      · exact ciInf_le hbelow_single xu
      · apply le_ciInf
        intro x'
        have hx' : (x' : X) = x₀ := by
          exact Finset.mem_singleton.mp x'.2
        rw [hx']
    rw [← hinf_eq]
    have habove_single :
        BddAbove
          (Set.range fun y' : Y => ⨅ x' : ({x₀} : Finset X), f (x' : X) (y' : Y)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨y', rfl⟩
      have hbelow_single_y' :
          BddBelow (Set.range fun x' : ({x₀} : Finset X) => f (x' : X) (y' : Y)) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨x', rfl⟩
        exact (h01 (x' : X) (x' : X).2 (y' : Y) (y' : Y).2).1
      let xu : ({x₀} : Finset X) := ⟨x₀, by simp⟩
      exact (ciInf_le hbelow_single_y' xu).trans
        ((h01 (x₀ : X) (x₀ : X).2 (y' : Y) (y' : Y).2).2)
    exact le_ciSup habove_single y

/-- No-regret proof route under the strengthened compact-continuous assumptions.

Here the finite-row inequality is supplied by no-regret, while compact approximation
is proved by a finite cover of `X`; this variant does not use the separation module.
It is still normalized because the current finite no-regret theorem assumes `0 ≤ f ≤ 1`. -/
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
