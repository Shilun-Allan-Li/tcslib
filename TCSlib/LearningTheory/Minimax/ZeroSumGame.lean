/-
Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karim Abdel Sadek, Mark Bedaywi
-/
import TCSlib.LearningTheory.Hedge.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite Two-Player Zero-Sum Games

## Main definitions

- `ZeroSumGame`: a finite two-player zero-sum game with payoffs in [0,1].
- `MixedStrategy`: a probability distribution over `Fin n` pure actions.
- `payoffVsPure`, `pureVsPayoff`: expected payoff of a mixed strategy against a pure action.
- `bestColumn`, `bestRow`: best pure responses to a mixed strategy.

## Main results

- `weak_duality`: for any mixed strategies `p`, `q` in a finite zero-sum game,
  the worst pure-column payoff against `p` is at most the best pure-row payoff
  against `q` (the trivial direction of the minimax theorem).

## References

* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*,
  Cambridge University Press, 2006. Chapter 7 (§7.1–7.2).
* [FS99] Y. Freund, R. E. Schapire, "Adaptive game playing using multiplicative
  weights", *Games and Economic Behavior* 29(1–2):79–103, 1999. Section 2.

Original formalization by Karim Abdel Sadek and Mark Bedaywi.
-/

open Real Finset BigOperators

/-! ## Game Setup -/

/-- A finite two-player zero-sum game with `M` row actions and `N` column actions,
given by a payoff matrix with entries in the interval `[0, 1]`. The row player wants
larger payoffs; the column player wants smaller payoffs. [CBL06, §7.1]; [FS99, §2].
Deviation: FS99's `M(i, j)` is the row player's loss (row minimizes); here entries are
payoffs and the row player maximizes. Entries are in `[0, 1]` as in FS99 (CBL06 allows
general bounded payoffs). -/
structure ZeroSumGame (M N : ℕ) where
  payoff : Fin M → Fin N → ℝ
  payoff_nonneg : ∀ i j, 0 ≤ payoff i j
  payoff_le_one : ∀ i j, payoff i j ≤ 1

/-- A mixed strategy over `n` pure actions: a probability distribution on `Fin n`,
kept as an explicit weight vector together with nonnegativity and the sum-to-one law.
[CBL06, §7.1]; [FS99, §2]. This is enough for finite games and avoids extra simplex
infrastructure. -/
structure MixedStrategy (n : ℕ) where
  weights : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  sum_one : ∑ i : Fin n, weights i = 1

/-- The expected payoff to the row player when the row plays the mixed strategy `p`
and the column plays the pure action `j`: the sum over rows `i` of `p i · A(i, j)`
(in matrix form, `pᵀ A e_j`). [CBL06, §7.1]; [FS99, §2]. -/
noncomputable def payoffVsPure {M N : ℕ} (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) : ℝ :=
  ∑ i : Fin M, p.weights i * G.payoff i j

/-- The expected payoff to the row player when the row plays the pure action `i` and
the column plays the mixed strategy `q`: the sum over columns `j` of `A(i, j) · q j`
(in matrix form, `e_iᵀ A q`). [CBL06, §7.1]; [FS99, §2]. -/
noncomputable def pureVsPayoff {M N : ℕ} (G : ZeroSumGame M N)
    (i : Fin M) (q : MixedStrategy N) : ℝ :=
  ∑ j : Fin N, G.payoff i j * q.weights j

/-- A pure column best response to the row mixed strategy `p`: a column `j` minimizing
the expected payoff `payoffVsPure G p j`. [FS99, §2 (best response)]. Finiteness lets
us choose an actual minimizer, not just an infimum. -/
noncomputable def bestColumn {M N : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) : Fin N :=
  Classical.choose (Finite.exists_min (payoffVsPure G p))

/-- The best-response column `bestColumn G p` does no worse for the column player than
any other column: its payoff against `p` is at most the payoff of any column `j`.
[FS99, §2 (best response)]. -/
lemma bestColumn_spec {M N : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) :
    payoffVsPure G p (bestColumn G p) ≤ payoffVsPure G p j := by
  exact (Classical.choose_spec (Finite.exists_min (payoffVsPure G p))) j

/-- A pure row best response to the column mixed strategy `q`: a row `i` maximizing
the expected payoff `pureVsPayoff G i q`. [FS99, §2 (best response)]. This is the
row-player analogue of `bestColumn`; it is currently unused elsewhere in the library. -/
noncomputable def bestRow {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (q : MixedStrategy N) : Fin M :=
  Classical.choose (Finite.exists_max (fun i : Fin M => pureVsPayoff G i q))

/-- The best-response row `bestRow G q` gets at least as much payoff against `q` as any
other row `i`. [FS99, §2 (best response)]. Currently unused elsewhere in the library. -/
lemma bestRow_spec {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (q : MixedStrategy N) (i : Fin M) :
    pureVsPayoff G i q ≤ pureVsPayoff G (bestRow G q) q := by
  exact (Classical.choose_spec (Finite.exists_max (fun i : Fin M => pureVsPayoff G i q))) i

/-! ## Weak Duality -/

/-- Weak duality: for any row mixed strategy `p` and column mixed strategy `q`, the
infimum over pure columns `j` of the payoff of `p` against `j` is at most the supremum
over pure rows `i` of the payoff of `i` against `q`. [CBL06, §7.2 (the trivial
direction `max min ≤ min max`)]; [FS99, §2].

**Proof sketch.** Let `v := Σᵢ Σⱼ pᵢ A(i, j) qⱼ` be the bilinear expected payoff of
`(p, q)`. Step 1: writing `v = Σⱼ payoff(p, j) · qⱼ` as a `q`-average over columns and
bounding each term below by the column infimum (which is bounded below by `0`) gives
`inf_j payoff(p, j) ≤ v`. Step 2: writing `v = Σᵢ payoff(i, q) · pᵢ` as a `p`-average
over rows and bounding each term above by the row supremum (bounded above by `1`) gives
`v ≤ sup_i payoff(i, q)`. Chain the two. -/
theorem weak_duality {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) (q : MixedStrategy N) :
    (⨅ j : Fin N, payoffVsPure G p j) ≤ ⨆ i : Fin M, pureVsPayoff G i q := by
  -- Put the bilinear expected payoff in the middle.  It is at least the worst
  -- pure-column payoff against `p`, and at most the best pure-row payoff
  -- against `q`.
  set v := ∑ i : Fin M, ∑ j : Fin N, p.weights i * G.payoff i j * q.weights j
  -- Step 1: the column infimum is at most `v` (average of `v` over columns).
  have hv_lb : ⨅ j, payoffVsPure G p j ≤ v := by
    -- Rewrite `v` as an average over columns and compare each term to the
    -- column infimum.
    have hv_eq : v = ∑ j : Fin N, payoffVsPure G p j * q.weights j := by
      simp only [v, payoffVsPure]; rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    rw [hv_eq]
    have hbdd : BddBelow (Set.range (payoffVsPure G p)) :=
      ⟨0, by rintro _ ⟨j, rfl⟩; exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (p.nonneg i) (G.payoff_nonneg i j)⟩
    calc ⨅ j, payoffVsPure G p j
        = (⨅ j, payoffVsPure G p j) * ∑ j, q.weights j := by rw [q.sum_one, mul_one]
      _ = ∑ j, (⨅ j, payoffVsPure G p j) * q.weights j := Finset.mul_sum ..
      _ ≤ ∑ j, payoffVsPure G p j * q.weights j :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (ciInf_le hbdd j) (q.nonneg j)
  -- Step 2: `v` is at most the row supremum (average of `v` over rows).
  have hv_ub : v ≤ ⨆ i, pureVsPayoff G i q := by
    -- Rewrite `v` as an average over rows and compare each term to the row
    -- supremum.
    have hv_eq : v = ∑ i : Fin M, pureVsPayoff G i q * p.weights i := by
      simp only [v, pureVsPayoff]; simp_rw [Finset.sum_mul]
      congr 1; ext i; congr 1; ext j; ring
    rw [hv_eq]
    have hbdd : BddAbove (Set.range (pureVsPayoff G · q)) :=
      ⟨1, by rintro _ ⟨i, rfl⟩
             calc ∑ j : Fin N, G.payoff i j * q.weights j
                 ≤ ∑ j : Fin N, 1 * q.weights j :=
                   Finset.sum_le_sum fun j _ =>
                     mul_le_mul_of_nonneg_right (G.payoff_le_one i j) (q.nonneg j)
               _ = 1 := by simp [q.sum_one]⟩
    calc ∑ i, pureVsPayoff G i q * p.weights i
        ≤ ∑ i, (⨆ i, pureVsPayoff G i q) * p.weights i :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (le_ciSup hbdd i) (p.nonneg i)
      _ = (⨆ i, pureVsPayoff G i q) := by
          rw [← Finset.mul_sum]; rw [p.sum_one, mul_one]
  linarith
