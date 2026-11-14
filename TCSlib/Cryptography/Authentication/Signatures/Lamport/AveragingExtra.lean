/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Optional-query and fair-bit position averaging

## Main definitions

None.

## Main results

* `optionQuery_favourable_expect_ge`: fresh forged messages have favourable fraction
  at least `1 / (2 |I|)`, with or without a query.
* `exists_position_fairBit_expect_ge`: some fixed position with a fresh fair bit performs
  at least as well as a uniform position and bit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 137.2. These are the counting and best-position steps of its reduction.
-/

namespace TCSlib.Cryptography.Authentication.LamportReduction

open TCSlib.Cryptography.Games

/-- If an optional queried message differs from the forged message, a uniform position and
bit avoids revealing the planted preimage and selects the forged preimage with probability
at least `1 / (2 |I|)`. An absent query imposes no avoidance constraint.
[PS10, proof of Theorem 137.2].

**Proof sketch.** With a query, freshness gives distinct messages and the differing-coordinate
bound applies. Without a query, half of the position-bit pairs select the forged preimage;
this is at least `1 / (2 |I|)` because the position type is nonempty. -/
theorem optionQuery_favourable_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
    (q : Option (ι → Bool)) (m' : ι → Bool) (hfresh : q ≠ some m') :
    1 / (2 * (Fintype.card ι : ℝ)) ≤
      ProbComp.expect (ProbComp.sample (ι × Bool))
        (fun p => if (∀ m, q = some m → m p.1 ≠ p.2) ∧ m' p.1 = p.2
          then (1 : ℝ) else 0) := by
  classical
  cases q with
  | none =>
    simp only [reduceCtorEq, false_implies, forall_const, true_and]
    rw [noQuery_expect_eq_half]
    have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card ι))
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  | some m =>
    have hne : m ≠ m' := by
      intro h
      exact hfresh (congrArg some h)
    simpa using (favourable_expect_ge hne)

/-- For every payoff `v(i,c)` on a nonempty finite position type and a bit, there is a
position whose average over a fair bit is at least the average over a uniform position and
fair bit. [PS10, proof of Theorem 137.2].

**Proof sketch.** Apply finite maximum averaging to the payoff already averaged over the bit.
The published product-sampling equation identifies its average over positions with the
uniform-pair expectation. -/
theorem exists_position_fairBit_expect_ge {ι : Type} [Fintype ι] [Nonempty ι]
    (v : ι → Bool → ℝ) :
    ∃ i, ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) ≤
      ProbComp.expect (ProbComp.sample Bool) (v i) := by
  obtain ⟨i, hi⟩ := exists_expect_sample_le
    (fun j : ι => ProbComp.expect (ProbComp.sample Bool) (v j))
  refine ⟨i, ?_⟩
  calc
    ProbComp.expect (ProbComp.sample (ι × Bool)) (fun p => v p.1 p.2) =
        ProbComp.expect
          ((ProbComp.sample ι).bind fun j =>
            (ProbComp.sample Bool).bind fun c => .pure (j, c)) (fun p => v p.1 p.2) :=
      (Bridge.expect_sample_pair (fun p : ι × Bool => v p.1 p.2)).symm
    _ = ProbComp.expect (ProbComp.sample ι)
        (fun j => ProbComp.expect (ProbComp.sample Bool) (v j)) := by
      simp only [ProbComp.expect_bind, ProbComp.expect_pure]
    _ ≤ ProbComp.expect (ProbComp.sample Bool) (v i) := hi

end TCSlib.Cryptography.Authentication.LamportReduction
