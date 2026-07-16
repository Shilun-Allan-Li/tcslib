import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open Real Finset BigOperators

def LossSeq (N T : ℕ) := Fin T → Fin N → ℝ

noncomputable def cumLoss {N T : ℕ} (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  ((Finset.univ (α := Fin T)).filter (fun s => s.val < t)).sum (fun s => ℓ s i)

noncomputable def hedgeWeight {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  Real.exp (-η * cumLoss ℓ t i)

noncomputable def potential {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) : ℝ :=
  ∑ i : Fin N, hedgeWeight η ℓ t i

noncomputable def hedgeDist {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) : ℝ :=
  hedgeWeight η ℓ t i / potential η ℓ t

lemma hedgeWeight_pos {N T : ℕ} (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 < hedgeWeight η ℓ t i := by
  exact exp_pos _

lemma potential_pos {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) :
    0 < potential η ℓ t := by
  apply Finset.sum_pos
  · intro i _
    exact hedgeWeight_pos η ℓ t i
  · exact Finset.univ_nonempty

lemma hedgeDist_nonneg {N T : ℕ} [NeZero N] (η : ℝ) (ℓ : LossSeq N T) (t : ℕ) (i : Fin N) :
    0 ≤ hedgeDist η ℓ t i :=
  div_nonneg (hedgeWeight_pos η ℓ t i).le (potential_pos η ℓ t).le
