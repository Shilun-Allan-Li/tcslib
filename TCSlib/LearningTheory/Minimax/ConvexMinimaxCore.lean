/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Minimax.FiniteMinimax
import Mathlib.Analysis.Convex.Jensen

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Real Finset BigOperators

namespace OnlineLearning

/-!
# Toward Convex-Compact Minimax

## Main results

- `finite_minimax_value`: extracts exact finite matrix-game value from the approximate minimax theorem proved via Hedge
- `finite_sampled_minimax_value`: applies the finite minimax theorem to a game sampled from a continuous payoff function
- `weak_convex_compact_minimax`: the easy minimax direction — lower value ≤ upper value for convex-compact games
- `exists_forall_le_of_finite_sublevel_intersections`: finite-intersection compactness step for sublevel sets in the row variable

## References

- Original formalization by Karim Abdel Sadek, Mark Bedaywi
-/

/-! ## Exact Value for Finite Matrix Games -/

/-!
The finite-game values are written with `iSup`/`iInf`, so we first provide a
canonical nonempty mixed strategy space.  The arbitrary strategy puts all mass
on one index chosen from `NeZero n`.
-/

/-- A concrete mixed strategy used only to prove that the type of mixed
strategies is nonempty.  It puts all mass on one arbitrary action. -/
noncomputable def arbitraryMixedStrategy (n : ℕ) [NeZero n] : MixedStrategy n where
  weights i := if i = Classical.choice inferInstance then 1 else 0
  nonneg i := by
    split <;> positivity
  sum_one := by
    classical
    let i₀ : Fin n := Classical.choice inferInstance
    change ∑ i : Fin n, (if i = i₀ then (1 : ℝ) else 0) = 1
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact False.elim (h (Finset.mem_univ _))

/-- The mixed-strategy space is nonempty whenever the underlying action set is
nonempty. -/
noncomputable instance mixedStrategyNonempty (n : ℕ) [NeZero n] :
    Nonempty (MixedStrategy n) :=
  ⟨arbitraryMixedStrategy n⟩

/-- Lower value of a finite zero-sum game: row chooses a mixed strategy, then
column chooses the worst pure response. -/
noncomputable def finiteLowerValue {M N : ℕ} (G : ZeroSumGame M N) : ℝ :=
  ⨆ p : MixedStrategy M, ⨅ j : Fin N, payoffVsPure G p j

/-- Upper value of a finite zero-sum game: column chooses a mixed strategy, then
row chooses the best pure response. -/
noncomputable def finiteUpperValue {M N : ℕ} (G : ZeroSumGame M N) : ℝ :=
  ⨅ q : MixedStrategy N, ⨆ i : Fin M, pureVsPayoff G i q

/-- Expected payoff against a pure column is nonnegative because payoffs and
mixed-strategy weights are nonnegative. -/
lemma payoffVsPure_nonneg {M N : ℕ} (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) :
    0 ≤ payoffVsPure G p j := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (p.nonneg i) (G.payoff_nonneg i j)

/-- Expected payoff against a pure column is at most one because every payoff is
at most one and the row mixed strategy has total mass one. -/
lemma payoffVsPure_le_one {M N : ℕ} (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) :
    payoffVsPure G p j ≤ 1 := by
  calc payoffVsPure G p j
      ≤ ∑ i : Fin M, p.weights i * 1 :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (G.payoff_le_one i j) (p.nonneg i)
    _ = 1 := by simp [p.sum_one]

/-- Expected payoff of a pure row against a mixed column is nonnegative. -/
lemma pureVsPayoff_nonneg {M N : ℕ} (G : ZeroSumGame M N)
    (i : Fin M) (q : MixedStrategy N) :
    0 ≤ pureVsPayoff G i q := by
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (G.payoff_nonneg i j) (q.nonneg j)

/-- Expected payoff of a pure row against a mixed column is at most one. -/
lemma pureVsPayoff_le_one {M N : ℕ} (G : ZeroSumGame M N)
    (i : Fin M) (q : MixedStrategy N) :
    pureVsPayoff G i q ≤ 1 := by
  calc pureVsPayoff G i q
      ≤ ∑ j : Fin N, 1 * q.weights j :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (G.payoff_le_one i j) (q.nonneg j)
    _ = 1 := by simp [q.sum_one]

/-- The set of row-guaranteed finite-game payoffs is bounded above by one. -/
lemma finiteLowerValue_bddAbove {M N : ℕ} [NeZero N] (G : ZeroSumGame M N) :
    BddAbove (Set.range fun p : MixedStrategy M => ⨅ j : Fin N, payoffVsPure G p j) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨p, rfl⟩
  have hbdd : BddBelow (Set.range (payoffVsPure G p)) :=
    ⟨0, by rintro _ ⟨j, rfl⟩; exact payoffVsPure_nonneg G p j⟩
  exact (ciInf_le hbdd (Classical.choice inferInstance)).trans (payoffVsPure_le_one G p _)

/-- The set of column-induced finite-game upper values is bounded below by
zero. -/
lemma finiteUpperValue_bddBelow {M N : ℕ} [NeZero M] (G : ZeroSumGame M N) :
    BddBelow (Set.range fun q : MixedStrategy N => ⨆ i : Fin M, pureVsPayoff G i q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hbdd : BddAbove (Set.range (fun i : Fin M => pureVsPayoff G i q)) :=
    ⟨1, by rintro _ ⟨i, rfl⟩; exact pureVsPayoff_le_one G i q⟩
  exact (pureVsPayoff_nonneg G (Classical.choice inferInstance) q).trans
    (le_ciSup hbdd (Classical.choice inferInstance))

/-- Weak duality for finite games: the lower value is always at most the upper
value. -/
lemma finiteLowerValue_le_upperValue {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N) :
    finiteLowerValue G ≤ finiteUpperValue G := by
  unfold finiteLowerValue finiteUpperValue
  apply ciSup_le
  intro p
  apply le_ciInf
  intro q
  exact weak_duality G p q

/-- Exact equality of finite game lower and upper values, obtained from the
arbitrarily good approximate saddle points produced by Hedge. -/
theorem finite_minimax_value {M N : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (hM : 1 < M) :
    finiteLowerValue G = finiteUpperValue G := by
  apply le_antisymm
  · exact finiteLowerValue_le_upperValue G
  · apply le_of_forall_pos_le_add
    intro ε hε
    -- The approximate minimax theorem gives strategies whose gap is at most
    -- `ε`.  Since this works for every positive `ε`, the exact values are equal.
    obtain ⟨p, q, hpq⟩ := approx_minimax G hM ε hε
    have hq_le :
        (⨆ i : Fin M, pureVsPayoff G i q) ≤
          (⨅ j : Fin N, payoffVsPure G p j) + ε := by
      have hbdd : BddAbove (Set.range (fun i : Fin M => pureVsPayoff G i q)) :=
        ⟨1, by rintro _ ⟨i, rfl⟩; exact pureVsPayoff_le_one G i q⟩
      apply ciSup_le
      intro i
      have hle_inf :
          pureVsPayoff G i q - ε ≤ ⨅ j : Fin N, payoffVsPure G p j := by
        apply le_ciInf
        intro j
        linarith [hpq i j]
      linarith
    have h_upper_at_q :
        finiteUpperValue G ≤ ⨆ i : Fin M, pureVsPayoff G i q := by
      unfold finiteUpperValue
      exact ciInf_le (finiteUpperValue_bddBelow G) q
    have h_lower_at_p :
        (⨅ j : Fin N, payoffVsPure G p j) ≤ finiteLowerValue G := by
      unfold finiteLowerValue
      exact le_ciSup (finiteLowerValue_bddAbove G) p
    linarith

/-! ## The Convex-Compact Target from the Writeup -/

/-- The exact minimax statement from the project writeup, specialized to
subsets of `ℝ`.

This is packaged as a `Prop` so that the target can be referenced while the
proof is developed in smaller lemmas. -/
def ConvexCompactMinimaxStatement (X Y : Set ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  (⨅ x : X, ⨆ y : Y, f x y) = (⨆ y : Y, ⨅ x : X, f x y)

section TargetAssumptions

variable (X Y : Set ℝ) (f : ℝ → ℝ → ℝ)

/-- Assumptions of Cesa-Bianchi--Lugosi Theorem 7.1, specialized to `ℝ`. -/
structure ConvexCompactMinimaxHypotheses : Prop where
  /-- The row set is nonempty. -/
  X_nonempty : X.Nonempty
  /-- The column set is nonempty. -/
  Y_nonempty : Y.Nonempty
  /-- Compactness of the row set is used for the finite-intersection argument. -/
  X_compact : IsCompact X
  /-- The row set is convex, so mixtures of row points stay in `X`. -/
  X_convex : Convex ℝ X
  /-- The column set is convex, so mixtures of column points stay in `Y`. -/
  Y_convex : Convex ℝ Y
  /-- For each column point, the payoff is continuous in the row variable. -/
  continuous_left : ∀ y ∈ Y, ContinuousOn (fun x => f x y) X
  /-- For each column point, the payoff is convex in the row variable. -/
  convex_left : ∀ y ∈ Y, ConvexOn ℝ X (fun x => f x y)
  /-- For each row point, the payoff is concave in the column variable. -/
  concave_right : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => f x y)
  /-- The payoff is bounded above on `X × Y`. -/
  bounded_above : BddAbove (Set.range fun xy : X × Y => f xy.1 xy.2)
  /-- The payoff is bounded below on `X × Y`. -/
  bounded_below : BddBelow (Set.range fun xy : X × Y => f xy.1 xy.2)

end TargetAssumptions

/-! ## Convex Combinations Written as Mixed Strategies -/

/-- A convex combination with coefficients from a mixed strategy stays inside a
convex set. -/
lemma mixed_sum_mem_convex {n : ℕ} (S : Set ℝ) (hS : Convex ℝ S)
    (p : MixedStrategy n) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ S) :
    (∑ i : Fin n, p.weights i * x i) ∈ S := by
  simpa [smul_eq_mul] using
    hS.sum_mem (t := Finset.univ) (w := p.weights) (z := x)
      (fun i _ => p.nonneg i) (by simpa using p.sum_one) (fun i _ => hx i)

/-- Jensen's inequality for a finite convex combination written using a mixed
strategy. -/
lemma convexOn_mixed_sum_le {n : ℕ} {S : Set ℝ} {g : ℝ → ℝ}
    (hg : ConvexOn ℝ S g) (p : MixedStrategy n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ S) :
    g (∑ i : Fin n, p.weights i * x i) ≤
      ∑ i : Fin n, p.weights i * g (x i) := by
  simpa [smul_eq_mul] using
    hg.map_sum_le (t := Finset.univ) (w := p.weights) (p := x)
      (fun i _ => p.nonneg i) (by simpa using p.sum_one) (fun i _ => hx i)

/-- The concave version of Jensen's inequality for a finite mixed-strategy
combination. -/
lemma concaveOn_le_mixed_sum {n : ℕ} {S : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ S g) (p : MixedStrategy n) (y : Fin n → ℝ)
    (hy : ∀ j, y j ∈ S) :
    (∑ j : Fin n, p.weights j * g (y j)) ≤
      g (∑ j : Fin n, p.weights j * y j) := by
  simpa [smul_eq_mul] using
    hg.le_map_sum (t := Finset.univ) (w := p.weights) (p := y)
      (fun j _ => p.nonneg j) (by simpa using p.sum_one) (fun j _ => hy j)

/-! ## Finite Samples of a Convex-Concave Game -/

/-- A finite matrix game obtained by restricting a payoff function to finite
families of row and column points. This version is for already-normalized
payoffs in `[0, 1]`; a general bounded payoff can be reduced to this by an
affine rescaling. -/
noncomputable def sampledGame {M N : ℕ} (f : ℝ → ℝ → ℝ)
    (x : Fin M → ℝ) (y : Fin N → ℝ)
    (h_nonneg : ∀ i j, 0 ≤ f (x i) (y j))
    (h_le_one : ∀ i j, f (x i) (y j) ≤ 1) : ZeroSumGame M N where
  payoff i j := f (x i) (y j)
  payoff_nonneg := h_nonneg
  payoff_le_one := h_le_one

/-- The finite minimax theorem applied to a sampled game. -/
theorem finite_sampled_minimax_value {M N : ℕ} [NeZero M] [NeZero N]
    (f : ℝ → ℝ → ℝ) (x : Fin M → ℝ) (y : Fin N → ℝ)
    (h_nonneg : ∀ i j, 0 ≤ f (x i) (y j))
    (h_le_one : ∀ i j, f (x i) (y j) ≤ 1) (hM : 1 < M) :
    finiteLowerValue (sampledGame f x y h_nonneg h_le_one) =
      finiteUpperValue (sampledGame f x y h_nonneg h_le_one) := by
  exact finite_minimax_value (sampledGame f x y h_nonneg h_le_one) hM

/-- If the row player mixes over sampled row points, convexity in the row
variable says the payoff at the mixed row point is no larger than the sampled
game payoff against a fixed column. -/
lemma sampled_payoffVsPure_ge_convex_combo {M N : ℕ}
    {X : Set ℝ} {f : ℝ → ℝ → ℝ} {x : Fin M → ℝ} {y : Fin N → ℝ}
    (h_nonneg : ∀ i j, 0 ≤ f (x i) (y j))
    (h_le_one : ∀ i j, f (x i) (y j) ≤ 1)
    (p : MixedStrategy M) (j : Fin N)
    (hf : ConvexOn ℝ X (fun x' => f x' (y j))) (hx : ∀ i, x i ∈ X) :
    f (∑ i : Fin M, p.weights i * x i) (y j) ≤
      payoffVsPure (sampledGame f x y h_nonneg h_le_one) p j := by
  simpa [payoffVsPure, sampledGame] using
    convexOn_mixed_sum_le (n := M) (S := X) (g := fun x' => f x' (y j)) hf p x hx

/-- If the column player mixes over sampled column points, concavity in the
column variable says the sampled expected payoff is no larger than the payoff
at the mixed column point. -/
lemma sampled_pureVsPayoff_le_concave_combo {M N : ℕ}
    {Y : Set ℝ} {f : ℝ → ℝ → ℝ} {x : Fin M → ℝ} {y : Fin N → ℝ}
    (h_nonneg : ∀ i j, 0 ≤ f (x i) (y j))
    (h_le_one : ∀ i j, f (x i) (y j) ≤ 1)
    (q : MixedStrategy N) (i : Fin M)
    (hf : ConcaveOn ℝ Y (fun y' => f (x i) y')) (hy : ∀ j, y j ∈ Y) :
    pureVsPayoff (sampledGame f x y h_nonneg h_le_one) i q ≤
      f (x i) (∑ j : Fin N, q.weights j * y j) := by
  simpa [pureVsPayoff, sampledGame, mul_comm] using
    concaveOn_le_mixed_sum (n := N) (S := Y) (g := fun y' => f (x i) y') hf q y hy

/-! ## The Universal Weak Minimax Inequality -/

/-- The easy minimax direction: for every fixed pair `(x, y)`, the lower value
at `y` is at most the upper value at `x`, so taking `sup` then `inf` preserves
the inequality. -/
lemma weak_convex_compact_minimax {X Y : Set ℝ} {f : ℝ → ℝ → ℝ}
    (h : ConvexCompactMinimaxHypotheses X Y f) :
    (⨆ y : Y, ⨅ x : X, f x y) ≤ (⨅ x : X, ⨆ y : Y, f x y) := by
  haveI : Nonempty X := h.X_nonempty.to_subtype
  haveI : Nonempty Y := h.Y_nonempty.to_subtype
  apply ciSup_le
  intro y
  apply le_ciInf
  intro x
  have hbelow_y : BddBelow (Set.range fun x' : X => f x' y) := by
    rcases h.bounded_below with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rintro _ ⟨x', rfl⟩
    exact ha ⟨(x', y), rfl⟩
  have habove_x : BddAbove (Set.range fun y' : Y => f x y') := by
    rcases h.bounded_above with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro _ ⟨y', rfl⟩
    exact hb ⟨(x, y'), rfl⟩
  exact (ciInf_le hbelow_y x).trans (le_ciSup habove_x y)

/-! ## Closed Sublevel Sets for the Compactness Step -/

/-- The closed subset of `X` where the payoff against `y` is at most `c`. -/
def minimaxSublevel (X : Set ℝ) (f : ℝ → ℝ → ℝ) (y c : ℝ) : Set ℝ :=
  X ∩ {x | f x y ≤ c}

/-- A sublevel set is contained in the ambient row set `X`. -/
lemma minimaxSublevel_subset (X : Set ℝ) (f : ℝ → ℝ → ℝ) (y c : ℝ) :
    minimaxSublevel X f y c ⊆ X := by
  intro x hx
  exact hx.1

/-- The sublevel set is closed when `X` is closed and the payoff is continuous
on `X` in the row variable. -/
lemma minimaxSublevel_isClosed {X : Set ℝ} {f : ℝ → ℝ → ℝ} {y c : ℝ}
    (hX : IsClosed X) (hf : ContinuousOn (fun x => f x y) X) :
    IsClosed (minimaxSublevel X f y c) := by
  simpa [minimaxSublevel, Set.preimage, Set.Iic] using
    hf.preimage_isClosed_of_isClosed hX (isClosed_Iic : IsClosed (Set.Iic c))

/-- A closed sublevel subset of a compact row set is compact. -/
lemma minimaxSublevel_isCompact {X : Set ℝ} {f : ℝ → ℝ → ℝ} {y c : ℝ}
    (hX : IsCompact X) (hf : ContinuousOn (fun x => f x y) X) :
    IsCompact (minimaxSublevel X f y c) := by
  exact hX.of_isClosed_subset (minimaxSublevel_isClosed hX.isClosed hf)
    (minimaxSublevel_subset X f y c)

/-- Finite-intersection compactness step: if every finite family of sublevel
constraints has a solution in `X`, then there is one point of `X` satisfying
all constraints at once. -/
lemma exists_forall_le_of_finite_sublevel_intersections {X Y : Set ℝ}
    {f : ℝ → ℝ → ℝ} (h : ConvexCompactMinimaxHypotheses X Y f) (c : ℝ)
    (hfin : ∀ u : Finset Y,
      (X ∩ ⋂ y ∈ u, minimaxSublevel X f y c).Nonempty) :
    ∃ x ∈ X, ∀ y : Y, f x y ≤ c := by
  have hclosed : ∀ y : Y, IsClosed (minimaxSublevel X f y c) := by
    intro y
    exact minimaxSublevel_isClosed h.X_compact.isClosed (h.continuous_left y y.2)
  rcases h.X_compact.inter_iInter_nonempty
      (fun y : Y => minimaxSublevel X f y c) hclosed hfin with ⟨x, hx⟩
  refine ⟨x, hx.1, ?_⟩
  intro y
  -- Membership in every sublevel set is exactly the pointwise bound `f x y ≤ c`.
  exact (Set.mem_iInter.mp hx.2 y).2

end OnlineLearning
