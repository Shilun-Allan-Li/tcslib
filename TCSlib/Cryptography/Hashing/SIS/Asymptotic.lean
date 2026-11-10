/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.CollisionOutput
import TCSlib.Cryptography.Hashing.SIS.Profiles
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Negligible raw collisions from the independent SIS assumption

## Main definitions

* `collisionAt`: a non-uniform PPT machine outputs an arbitrary raw collision word
  on the actual canonical uniform matrix challenge.

## Main results

Exact polynomial column schedules and the existing signed postprocessor turn the
independent SIS assumption into negligible collision probability. The explicit dyadic
profile supplies the numerical premises for the same reduction.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  observations after Equation (4.1.1), Section 5.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Definition 26.8 (non-uniform polynomial-time adversaries).

The numeric family has no automatic uniform-parameter or fair-bit sampler claim.
This theorem uses the exact mathematical uniform matrix law of `SISAssumption`;
the dyadic sampling and evaluator modules provide separate implementation obligations.
No generic CRH interface, LWE hypothesis, SIS--LWE bridge or hardness theorem is added.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open Complexity
open TCSlib.Cryptography.SIS (Family)

/-- Collision success at parameter `κ` uses the actual machine output after the
existing false-padding and splitting conventions [Pei16, Section 5.1, machine adaptation]. -/
noncomputable def collisionAt (F : Family) (D : NUPPT) (κ : ℕ) : ℝ :=
  collisionProbability (F.parameters κ) (fun A r =>
    rawCollisionInputs (F.parameters κ).columns
      (D.runAt κ (TCSlib.Cryptography.SIS.encodeChallenge (F.parameters κ)
        (F.residueBits.eval κ) A) r))

/-- The complete collision experiment retains the machine's original advice and coins. -/
theorem collisionAt_eq (F : Family) (D : NUPPT) (κ : ℕ) :
    collisionAt F D κ = collisionProbability (F.parameters κ) (fun A r =>
      rawCollisionInputs (F.parameters κ).columns
        (D.runAt κ (TCSlib.Cryptography.SIS.encodeChallenge (F.parameters κ)
          (F.residueBits.eval κ) A) r)) := rfl

/-- Under the independent SIS assumption, every non-uniform PPT raw collision finder
has negligible success for an exact polynomial column schedule
[Pei16, observations after Equation (4.1.1), Section 5.1].

**Proof sketch.** Use `NUPPT.exists_compParam` with identity argument preprocessing
and `collisionOutputPoly M F.magnitudeBits` as parameter-aware postprocessing. Its
FP theorem uses only the existing public loop host. The returned machine keeps the finder's
advice and coins; transport their public equations and apply the exact same-seed raw
collision bound at every parameter. `SISAssumption` bounds that solver negligibly,
and collision probabilities are nonnegative and pointwise no larger. No uniform
choice of a worst adversary/message and no stronger assumption is needed. -/
theorem negligible_collisions_of_SIS (F : Family) (M : PolyExpr)
    (hcolumns : ∀ κ, (F.parameters κ).columns = M.eval κ)
    (hbound : ∀ κ, (F.parameters κ).columns ≤ (F.parameters κ).sqNormBound)
    (hwidth : ∀ κ, 0 < F.magnitudeBits.eval κ)
    (hSIS : TCSlib.Cryptography.SIS.SISAssumption F) (D : NUPPT) :
    Negligible (fun κ => collisionAt F D κ) := by
  obtain ⟨solver, hcoins, _, _, hrun⟩ :=
    D.exists_compParam polyTimeComputable_pairSndD
      (polyTimeComputable_collisionOutputPoly M F.magnitudeBits)
  have dominates (κ : ℕ) : collisionAt F D κ ≤ F.successAt solver κ := by
    let P := F.parameters κ
    let challenge (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)) :=
      TCSlib.Cryptography.SIS.encodeChallenge P (F.residueBits.eval κ) A
    let find (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)) (r : D.Coins κ) :=
      D.runAt κ (challenge A) r
    have hraw := rawCollisionProbability_le_successProbability P M F.magnitudeBits
      (List.replicate κ true) find
      (by simpa only [List.length_replicate] using hcolumns κ)
      (by simpa only [List.length_replicate] using hwidth κ) (hbound κ)
    rw [collisionAt_eq]
    refine hraw.trans_eq ?_
    rw [Family.successAt_eq, TCSlib.Cryptography.SIS.successProbability_eq,
      TCSlib.Cryptography.SIS.successProbability_eq]
    let e := (Equiv.refl (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))).prodCongr
      (NUPPT.coinsCongr hcoins.symm κ)
    rw [← uprob_comp_equiv e]
    congr 1
    funext z
    simp only [e, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
      NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn, hrun, NUPPT.advInput_eq,
      pairSndD_pairEncode, List.length_replicate, find, challenge, P]
  apply ((TCSlib.Cryptography.SIS.sisAssumption_iff F).mp hSIS solver).mono
  refine ⟨0, fun κ _ => ?_⟩
  have hnonneg : 0 ≤ collisionAt F D κ := by
    rw [collisionAt_eq, collisionProbability_eq]
    exact uprob_nonneg _
  rw [abs_of_nonneg hnonneg, abs_of_nonneg (hnonneg.trans (dominates κ))]
  exact dominates κ

/-- The explicit dyadic profile has negligible raw collisions under its own independent
SIS assumption [Pei16, Section 5.1, disclosed dyadic specialization].

**Proof sketch.** Its public readers identify the exact column polynomial, the
equal squared-norm budget, and a positive magnitude width at every parameter.
Apply `negligible_collisions_of_SIS`. This hypothesis is not derived from LWE. -/
theorem dyadic_collision_negligible
    (hSIS : TCSlib.Cryptography.SIS.SISAssumption dyadicFamily) (D : NUPPT) :
    Negligible (fun κ => collisionAt dyadicFamily D κ) := by
  refine negligible_collisions_of_SIS dyadicFamily dyadicFamily.columnsBound
    ?_ ?_ ?_ hSIS D
  · intro κ
    rw [dyadicFamily_parameters, dyadicParameters_columns, dyadicFamily_columnsBound,
      PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow, PolyExpr.eval_add,
      PolyExpr.eval_var, PolyExpr.eval_const]
  · intro κ
    rw [dyadicFamily_parameters, dyadicParameters_columns, dyadicParameters_sqNormBound]
  · intro κ
    rw [dyadicFamily_magnitudeBits, PolyExpr.eval_add, PolyExpr.eval_const]
    exact Nat.zero_lt_succ _

end TCSlib.Cryptography.Hashing.SIS
