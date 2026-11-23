/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.Covering
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.LocallyConvex

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Antipodal obstructions for continuous circle-valued maps

## Main definitions

No new definitions.

## Main results

* `not_exists_continuous_angle_antipodal`: an antipodal circle-valued map
  on a nonempty preconnected space has no continuous real angle.
* `exists_ne_zero_eq_zero_of_odd`: a complex-valued map on punctured
  three-dimensional parameter space that is continuous and odd has a zero.

## References

* Mathlib, `Mathlib.Topology.Covering`, `IsCoveringMap.const_of_comp`:
  constancy of continuous lifts into a single covering fiber.
* [Hat02] A. Hatcher, *Algebraic Topology*, Cambridge University Press,
  2002, Theorem 1.10 and Proposition 1.34.
-/

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- On a nonempty preconnected space with a continuous involution,
no continuous real-valued angle can represent a circle-valued map that
changes to its antipode under the involution. This is a technical
consequence of uniqueness of covering lifts [Hat02, Prop. 1.34].

**Proof sketch.** Suppose such an angle `θ` exists. The continuous
difference `δ x = θ (a x) - θ x` has constant circle exponential, whose
complex value is `-1`. Rigidity of lifts through the circle covering makes
`δ` constant. Involutivity gives `δ (a x) = -δ x`, so that constant is zero.
Its exponential would therefore have complex value both `1` and `-1`,
a contradiction. -/
theorem not_exists_continuous_angle_antipodal
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    (a : X → X) (ha : Continuous a) (hinv : Function.Involutive a) :
    ¬ ∃ θ : X → ℝ, Continuous θ ∧
      ∀ x : X,
        (Circle.exp (θ (a x)) : ℂ) = -(Circle.exp (θ x) : ℂ) :=
  (by
  rintro ⟨θ, hθ, hodd⟩
  let δ : X → ℝ := fun x => θ (a x) - θ x
  have hδ : Continuous δ := (hθ.comp ha).sub hθ
  have hexp (x : X) : (Circle.exp (δ x) : ℂ) = -1 := by
    rw [show δ x = θ (a x) - θ x from rfl,
      Circle.exp_sub, Circle.coe_div, hodd x]
    simp
  have hconst (x y : X) : δ x = δ y :=
    isCoveringMap_circleExp.const_of_comp hδ
      (fun x y => Circle.coe_injective ((hexp x).trans (hexp y).symm)) x y
  obtain ⟨x⟩ := ‹Nonempty X›
  have hzero : δ x = 0 := by
    have h := hconst (a x) x
    change θ (a (a x)) - θ (a x) = θ (a x) - θ x at h
    rw [hinv x] at h
    change θ (a x) - θ x = 0
    linarith
  have hcomplex := hexp x
  rw [hzero, Circle.exp_zero, Circle.coe_one] at hcomplex
  norm_num at hcomplex
)


/-- A complex-valued map on three-dimensional real space that is
continuous away from zero and odd at every nonzero parameter has a zero
away from the origin. This is the punctured-space odd-map formulation of
the two-dimensional Borsuk–Ulam theorem [Hat02, Thm. 1.10].

**Proof sketch.** Suppose the map never vanishes away from the origin.
Map the whole complex plane into punctured parameter space by
`z ↦ (z, 1 - ‖z‖)`, and normalize the resulting nonzero complex values
to the unit circle. The complex plane is contractible and locally path
connected, so this circle-valued map admits a continuous real angle.
Restrict the angle to the unit circle, where the parameter map is
`z ↦ (z, 0)` and sends antipodes to opposite nonzero parameters.
Oddness makes this restricted angle antipodal, contradicting the
continuous-angle obstruction. -/
theorem exists_ne_zero_eq_zero_of_odd
    (F : ℂ × ℝ → ℂ)
    (hF : ContinuousOn F {p : ℂ × ℝ | p ≠ 0})
    (hodd : ∀ p : ℂ × ℝ, p ≠ 0 → F (-p) = -F p) :
    ∃ p : ℂ × ℝ, p ≠ 0 ∧ F p = 0 :=
  (by
  by_contra! hnone
  let P : ℂ → ℂ × ℝ := fun z => (z, 1 - ‖z‖)
  have hP : Continuous P := continuous_id.prodMk (continuous_const.sub continuous_norm)
  have hPne (z : ℂ) : P z ≠ 0 := by
    intro h
    have hz : z = 0 := congrArg Prod.fst h
    have ht : 1 - ‖z‖ = 0 := congrArg Prod.snd h
    rw [hz, norm_zero] at ht
    norm_num at ht
  let g : ℂ → ℂ := fun z => F (P z)
  have hg : Continuous g := hF.comp_continuous hP hPne
  have hgne (z : ℂ) : g z ≠ 0 := hnone (P z) (hPne z)
  let N : ℂ → Circle := fun z =>
    ⟨g z / (‖g z‖ : ℂ), by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr (hgne z))]⟩
  have hN : Continuous N :=
    (hg.div (Complex.continuous_ofReal.comp hg.norm)
      (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hgne z)))).subtype_mk _
  obtain ⟨θ, hθ, hlift⟩ := exists_continuous_angle N hN
  let A : Circle → Circle := fun z =>
    ⟨-(z : ℂ), mem_sphere_zero_iff_norm.mpr (by rw [norm_neg, Circle.norm_coe])⟩
  have hA : Continuous A := continuous_subtype_val.neg.subtype_mk _
  have hAinv : Function.Involutive A := by
    intro z
    apply Subtype.ext
    exact neg_neg (z : ℂ)
  have hsurj : Function.Surjective Circle.exp := fun z =>
    ⟨(z : ℂ).arg, Circle.exp_arg z⟩
  letI : ConnectedSpace Circle := hsurj.connectedSpace Circle.exp.continuous
  apply (not_exists_continuous_angle_antipodal A hA hAinv)
  refine ⟨fun z => θ (z : ℂ), hθ.comp continuous_subtype_val, ?_⟩
  intro z
  rw [hlift, hlift]
  have hgodd : g (-(z : ℂ)) = -g (z : ℂ) := by
    change F (P (-(z : ℂ))) = -F (P (z : ℂ))
    have hPneg : P (-(z : ℂ)) = -P (z : ℂ) := by
      dsimp only [P]
      simp only [norm_neg, Circle.norm_coe, sub_self, Prod.neg_mk, neg_zero]
    rw [hPneg]
    exact hodd _ (hPne _)
  change g (-(z : ℂ)) / (‖g (-(z : ℂ))‖ : ℂ) =
    -(g (z : ℂ) / (‖g (z : ℂ)‖ : ℂ))
  rw [hgodd, norm_neg, neg_div]
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
