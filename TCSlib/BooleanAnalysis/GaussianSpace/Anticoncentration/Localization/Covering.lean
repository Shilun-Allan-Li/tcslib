/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Covering
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Local product decompositions of additive group homomorphisms

## Main definitions

No new definitions.

## Main results

* `exists_homeomorph_preimage_prod_ker`: a continuous local section
  identifies its preimage with the section domain times the kernel.

* `isCoveringMap_of_surjective_of_isLocalHomeomorph`: the group covering criterion.

* `isCoveringMap_circleExp`: the real exponential covers the complex unit circle.

* `exists_continuous_angle`: circle-valued maps on simply connected spaces lift to real angles.

## References

* Mathlib, `Mathlib.Topology.Algebra.Group.Basic`:
  continuous group operations and translation homeomorphisms.
* [CdH16] Y. Cornulier and P. de la Harpe, *Metric geometry of locally compact
  groups*, arXiv:1403.3796v4 (2016), Proposition 2.D.2.
* Mathlib, `Mathlib.Topology.Homotopy.Lifting`:
  continuous lifting from simply connected, locally path-connected spaces.
* [Hat02] A. Hatcher, *Algebraic Topology*, Cambridge University Press,
  2002, Proposition 1.33.
-/

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- A continuous section of an additive group homomorphism over a set `U`
identifies the preimage of `U` homeomorphically with `U` times the kernel,
with first coordinate given by the homomorphism.

No openness or discreteness assumption is needed for this product
decomposition.

**Proof sketch.** Send a point `x` to
`(f x, -σ (f x) + x)`. The second coordinate belongs to the kernel
because `σ` is a section. The inverse sends `(u, k)` to `σ u + k`.
The section identity and group laws prove that these maps are inverse;
continuity follows from the continuous section, homomorphism, and group
operations. -/
theorem exists_homeomorph_preimage_prod_ker
    {G H : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G]
    [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (f : G →+ H) (hf : Continuous f)
    (U : Set H) (σ : U → G) (hσ : Continuous σ)
    (hsection : ∀ u : U, f (σ u) = (u : H)) :
    ∃ e : (f ⁻¹' U) ≃ₜ (U × f.ker),
      ∀ x : f ⁻¹' U, ((e x).1 : H) = f (x : G) :=
  (by
  let u : (f ⁻¹' U) → U := fun x => ⟨f (x : G), x.property⟩
  let k : (f ⁻¹' U) → f.ker := fun x =>
    ⟨-σ (u x) + (x : G), by
      change f (-σ (u x) + (x : G)) = 0
      rw [map_add, map_neg, hsection]
      exact neg_add_cancel _⟩
  let j : U × f.ker → (f ⁻¹' U) := fun y =>
    ⟨σ y.1 + (y.2 : G), by
      change f (σ y.1 + (y.2 : G)) ∈ U
      rw [map_add, hsection, (show f (y.2 : G) = 0 from y.2.property), add_zero]
      exact y.1.property⟩
  have hu : Continuous u := (hf.comp continuous_subtype_val).subtype_mk _
  have hk : Continuous k :=
    ((hσ.comp hu).neg.add continuous_subtype_val).subtype_mk _
  have hj : Continuous j :=
    ((hσ.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have huj (y : U × f.ker) : u (j y) = y.1 := by
    apply Subtype.ext
    change f (σ y.1 + (y.2 : G)) = (y.1 : H)
    rw [map_add, hsection, (show f (y.2 : G) = 0 from y.2.property), add_zero]
  refine ⟨
    { toFun := fun x => (u x, k x)
      invFun := j
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := hu.prodMk hk
      continuous_invFun := hj }, ?_⟩
  · intro x
    apply Subtype.ext
    change σ (u x) + (-σ (u x) + (x : G)) = (x : G)
    simp
  · intro y
    apply Prod.ext
    · exact huj y
    · apply Subtype.ext
      change -σ (u (j y)) + (σ y.1 + (y.2 : G)) = (y.2 : G)
      rw [huj]
      simp
  · intro x
    rfl
)


/-- A surjective additive group homomorphism between topological groups
is a covering map if its underlying map is a local homeomorphism.
[CdH16, Prop. 2.D.2], in additive notation and with the local-homeomorphism
hypothesis imposed everywhere rather than only at the identity.

**Proof sketch.** The kernel is discrete: restrict the local homeomorphism
to the kernel, whose image is the singleton zero. At any target point,
surjectivity supplies a preimage, and a local inverse chart around that
preimage supplies a continuous section on an open neighborhood.
The section product decomposition identifies the neighborhood's preimage
with the neighborhood times the discrete kernel, respecting projection.
Thus every target point has an evenly covered neighborhood. -/
theorem isCoveringMap_of_surjective_of_isLocalHomeomorph
    {G H : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G]
    [AddGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (f : G →+ H) (hsurj : Function.Surjective f)
    (hloc : IsLocalHomeomorph f) :
    IsCoveringMap f :=
  (by
  have himage : Set.image f (f.ker : Set G) = ({0} : Set H) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · rintro rfl
      exact ⟨0, by simp, map_zero f⟩
  letI : DiscreteTopology (Set.image f (f.ker : Set G)) := by
    rw [himage]
    infer_instance
  letI : DiscreteTopology f.ker := hloc.isLocalHomeomorphOn.discreteTopology_of_image
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  obtain ⟨e, hxe, he⟩ := hloc x
  let σ : e.target → G := fun u => e.symm u
  have hσ : Continuous σ := continuousOn_iff_continuous_restrict.mp e.continuousOn_symm
  have hsection (u : e.target) : f (σ u) = (u : H) := by
    rw [he]
    exact e.right_inv u.property
  obtain ⟨E, hE⟩ := exists_homeomorph_preimage_prod_ker f hloc.continuous
    e.target σ hσ hsection
  have hy : y ∈ e.target := by
    rw [← hx, he]
    exact e.map_source hxe
  have hcov : IsEvenlyCovered f y f.ker :=
    ⟨inferInstance, e.target, hy, e.open_target,
      e.open_target.preimage hloc.continuous, E, hE⟩
  exact hcov.to_isEvenlyCovered_preimage
)


/-- The exponential map from the real line to the complex unit circle
is a covering map, specializing [CdH16, Prop. 2.D.2].

**Proof sketch.** Regard the circle as an additive topological group
using the existing exponential homomorphism. Its argument function
supplies a preimage of every circle point, and the exponential map is
already known to be a local homeomorphism. Apply the covering theorem
for surjective local-homeomorphic additive group homomorphisms. -/
theorem isCoveringMap_circleExp : IsCoveringMap Circle.exp :=
  (by
  change IsCoveringMap (Circle.expHom : ℝ → Additive Circle)
  apply isCoveringMap_of_surjective_of_isLocalHomeomorph Circle.expHom
  · intro z
    exact ⟨(z.toMul : ℂ).arg, Circle.exp_arg z.toMul⟩
  · exact isLocalHomeomorph_circleExp
)


/-- Every continuous circle-valued map on a simply connected, locally
path-connected space admits a continuous real-valued angle, specializing
the covering lifting criterion [Hat02, Prop. 1.33].

**Proof sketch.** Choose a basepoint and use the argument of its image as
an initial lift. Apply the covering-space lifting theorem to the circle
exponential covering, then read the resulting continuous lift pointwise. -/
theorem exists_continuous_angle
    {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    (f : X → Circle) (hf : Continuous f) :
    ∃ θ : X → ℝ, Continuous θ ∧
      ∀ x : X, Circle.exp (θ x) = f x :=
  (by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨θ, hθ, _⟩ := isCoveringMap_circleExp.existsUnique_continuousMap_lifts
    (⟨f, hf⟩ : ContinuousMap X Circle) x₀ (f x₀ : ℂ).arg (Circle.exp_arg (f x₀))
  refine ⟨θ, θ.continuous, ?_⟩
  intro x
  exact congrFun hθ.2 x
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
