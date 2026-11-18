/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Samplers
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Load
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Defs
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Bounds
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Conditions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The uniformly small JLS error event

## Main definitions

* The three failure events, the exact joint law, and `Params.errProb`.

## Contents

* `Claim42.Load`: finite binomial and bucket-tail bounds.
* `Claim42.Defs`: failure events, joint law, and locality bounds.
* `Claim42.Bounds`: rounded bucket counts and numerical tail bounds.
* `Claim42.Conditions`: conditional event estimates and decomposition.

## Main results

* `Params.claim42`: eventual error at most 2^(-κ), uniformly in the public prime.
* Locality/Markov and event-decomposition statements support the error analysis.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open TCSlib.Cryptography.Games
open scoped BigOperators

namespace Params

/-- For all sufficiently large κ the error event has probability at most 2^(-κ),
uniformly in every public prime [JLS26, Claim 4.2, pp. 19-21]. Dv3 uses the rounded
rational noise schedule (SP-W1); Dv7 makes the common eventual threshold explicit.

**Proof sketch.** Use the three-event decomposition. Locality and Markov bound Cond1,
conditionally on each fixed generator index. Independent noise repetitions then bound
simultaneous Cond1. Bucket-tail bounds control Cond2 outside Cond1 and the common Cond3.
The bucket count is polynomial; logarithmic growth and the resulting exponential bounds
make their sum at most 2^(-κ), with no dependence on pp. -/
theorem claim42 (P : Params) {cLoc : ℕ} (hLoc : P.R.HasLocality cLoc) :
    ∃ κ₀, ∀ κ ≥ κ₀, ∀ pp : PrimeParam κ,
      P.errProb κ pp ≤ (2 : ℝ)⁻¹ ^ κ := by
  classical
  obtain ⟨κΓ, hΓ⟩ := P.Γ_le_B
  obtain ⟨κlog, hlog⟩ := P.le_log_n (4 * cLoc)
  obtain ⟨κpoly, hpoly⟩ := Internal.prefactor_eventually_le_two_pow P
  refine ⟨max 12 (max κΓ (max κlog κpoly)), ?_⟩
  intro κ hκ pp
  have hcuts : 12 ≤ κ ∧ κΓ ≤ κ ∧ κlog ≤ κ ∧ κpoly ≤ κ := ?_
  swap
  · omega
  rcases hcuts with ⟨h12, hκΓ, hκlog, hκpoly⟩
  have h3 := Internal.cond3_joint_le_quarter_pow P κ pp h12
  have h1 := Internal.cond1_all_joint P hLoc κ pp (hlog κ hκlog)
  have hsum :
      (∑ k : Fin κ, Games.ProbComp.prob (P.jointLaw κ pp)
        (fun x => P.Cond2 κ pp x.1 x.2.draw k ∧
          ¬ P.Cond1 κ pp x.1 x.2.draw k)) ≤
        (κ : ℝ) * ((P.B κ : ℝ) * (4 : ℝ)⁻¹ ^ κ) := ?_
  swap
  · refine (Finset.sum_le_sum (fun k _ =>
      Internal.cond2_sparse_joint_le_quarter_pow P κ pp k h12 (hΓ κ hκΓ))).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, le_refl]
  have hcoarse : P.errProb κ pp ≤
      (((κ + 1) * P.B κ + 1 : ℕ) : ℝ) * (4 : ℝ)⁻¹ ^ κ := ?_
  swap
  · have hd := P.errProb_le_decomposition κ pp
    push_cast
    nlinarith
  have hnonneg : (0 : ℝ) ≤ (4 : ℝ)⁻¹ ^ κ := ?_
  swap
  · positivity
  have hfinal : (((κ + 1) * P.B κ + 1 : ℕ) : ℝ) * (4 : ℝ)⁻¹ ^ κ ≤
      (2 : ℝ)⁻¹ ^ κ := ?_
  swap
  · refine (mul_le_mul_of_nonneg_right (hpoly κ hκpoly) hnonneg).trans_eq ?_
    rw [← mul_pow]
    congr 1
    norm_num
  exact hcoarse.trans hfinal

end Params
end TCSlib.Cryptography.Obfuscation.StructuredSeed
