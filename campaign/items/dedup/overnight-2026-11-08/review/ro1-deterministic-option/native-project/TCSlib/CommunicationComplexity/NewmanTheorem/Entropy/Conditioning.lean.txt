/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.Basic
import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.ChainRules

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Entropy: conditioning and invariance lemmas

Invariance lemmas for conditional entropy `H[X | Z ; μ]` and conditional mutual information
`I[X : Y | Z ; μ]`, built on the PFR project's definitions (natural-logarithm units
throughout): almost-everywhere congruence, invariance under identical distribution, injective
recoding of the conditioning variable, and transfer of identical distribution through
conditioning on an event. This is the third part of the information-theoretic toolkit used by
the randomized lower bound for disjointness in
`TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound`; the basic bounds
are in `TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.Basic` and the chain rules in
`TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.ChainRules`.

## Main definitions

None.

## Main results

- `condEntropy_congr_ae`: conditional entropy is unchanged under almost-everywhere
  replacement of both arguments
- `condMutualInfo_congr_ae_left_right`: conditional mutual information is unchanged under
  almost-everywhere replacement of the two non-conditioning arguments
- `condMutualInfo_congr_ae`: conditional mutual information is unchanged under
  almost-everywhere replacement of all three arguments
- `condMutualInfo_congr_ae_finite`: the same, for finite alphabets
- `IdentDistrib.condMutualInfo_eq`: conditional mutual information depends only on the joint
  law of the triple
- `IdentDistrib.condMutualInfo_eq_finite`: the same, for finite alphabets
- `condMutualInfo_comp_right_conditioning_of_injective`: conditional mutual information is
  invariant under injective recodings of the conditioning variable
- `IdentDistrib.cond_of_pair`: conditioning identically distributed pairs on the same event
  in the second coordinate preserves identical distribution of the first coordinate

## Naming note

`IdentDistrib.condMutualInfo_eq` is declared inside `namespace ProbabilityTheory`, so its
full name is `ProbabilityTheory.IdentDistrib.condMutualInfo_eq`. Wherever the namespace
`ProbabilityTheory.IdentDistrib` is open (in particular inside the body of that lemma and in
later `IdentDistrib.*` declarations) the short name `condMutualInfo_eq` resolves to it and
shadows PFR's `ProbabilityTheory.condMutualInfo_eq` (the identity
`I[X : Y | Z] = H[X | Z] + H[Y | Z] - H[X, Y | Z]`). Proofs that need the PFR lemma write
`_root_.ProbabilityTheory.condMutualInfo_eq`.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [CT06] T. M. Cover, J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  Wiley, 2006.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace ProbabilityTheory

open MeasureTheory Measure Set

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

variable {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  {W : Ω → V}

/-- Conditional entropy is unchanged when both variables are replaced by almost-everywhere equal
variables. -/
theorem condEntropy_congr_ae
    {X' : Ω → S} {Y' : Ω → T}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange X'] [FiniteRange Y']
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (hXae : X =ᵐ[μ] X') (hYae : Y =ᵐ[μ] Y') :
    H[X | Y ; μ] = H[X' | Y' ; μ] := by
  have hpair :
      IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y' ω)) μ μ :=
    IdentDistrib.of_ae_eq (hX.prodMk hY).aemeasurable (hXae.prodMk hYae)
  exact IdentDistrib.condEntropy_eq hX hY hX' hY' hpair

/-- Conditional mutual information is unchanged when the two measured variables are replaced by
almost-everywhere equal variables and the conditioning variable is unchanged. -/
theorem condMutualInfo_congr_ae_left_right
    {X' : Ω → S} {Y' : Ω → T}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange X'] [FiniteRange Y']
    [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y')
    (hXae : X =ᵐ[μ] X') (hYae : Y =ᵐ[μ] Y') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z ; μ] := by
  rw [condMutualInfo_eq hX hY hZ, condMutualInfo_eq hX' hY' hZ]
  have hXcond :
      H[X | Z ; μ] = H[X' | Z ; μ] := by
    exact condEntropy_congr_ae hX hZ hX' hZ hXae (by rfl)
  have hYcond :
      H[Y | Z ; μ] = H[Y' | Z ; μ] := by
    exact condEntropy_congr_ae hY hZ hY' hZ hYae (by rfl)
  have hXYcond :
      H[fun ω => (X ω, Y ω) | Z ; μ] = H[fun ω => (X' ω, Y' ω) | Z ; μ] := by
    exact condEntropy_congr_ae (hX.prodMk hY) hZ (hX'.prodMk hY') hZ
      (hXae.prodMk hYae) (by rfl)
  rw [hXcond, hYcond, hXYcond]

/-- Conditional mutual information is unchanged when all three variables are replaced by
almost-everywhere equal variables: if `X = X'`, `Y = Y'` and `Z = Z'` almost surely, then
`I(X : Y | Z) = I(X' : Y' | Z')`.

**Proof sketch.** Expand both sides as `H(X | Z) + H(Y | Z) − H((X, Y) | Z)` and replace each of
the three conditional entropies by its primed counterpart using `condEntropy_congr_ae` (for the
pair, the almost-everywhere equality of the pairs is assembled from the two components). -/
theorem condMutualInfo_congr_ae
    {X' : Ω → S} {Y' : Ω → T} {Z' : Ω → U}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    [FiniteRange X'] [FiniteRange Y'] [FiniteRange Z']
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y') (hZ' : Measurable Z')
    (hXae : X =ᵐ[μ] X') (hYae : Y =ᵐ[μ] Y') (hZae : Z =ᵐ[μ] Z') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z' ; μ] := by
  rw [condMutualInfo_eq (μ := μ) hX hY hZ,
    condMutualInfo_eq (μ := μ) hX' hY' hZ']
  have hXcond :
      H[X | Z ; μ] = H[X' | Z' ; μ] := by
    exact condEntropy_congr_ae hX hZ hX' hZ' hXae hZae
  have hYcond :
      H[Y | Z ; μ] = H[Y' | Z' ; μ] := by
    exact condEntropy_congr_ae hY hZ hY' hZ' hYae hZae
  have hXYcond :
      H[fun ω => (X ω, Y ω) | Z ; μ] = H[fun ω => (X' ω, Y' ω) | Z' ; μ] := by
    exact condEntropy_congr_ae (hX.prodMk hY) hZ (hX'.prodMk hY') hZ'
      (hXae.prodMk hYae) hZae
  rw [hXcond, hYcond, hXYcond]

/-- Conditional mutual information is unchanged when all three variables are replaced by
almost-everywhere equal variables, on a finite measurable sample space with finite alphabets:
if `X = X'`, `Y = Y'` and `Z = Z'` almost surely then `I(X : Y | Z) = I(X' : Y' | Z')`. This is
the finite-space form of `condMutualInfo_congr_ae`, which infers measurability from the finite
measurable sample space and the finite-range hypotheses from the finite alphabets. -/
theorem condMutualInfo_congr_ae_finite
    {X' : Ω → S} {Y' : Ω → T} {Z' : Ω → U}
    [CommunicationComplexity.FiniteMeasureSpace Ω]
    [Finite S] [Finite T] [Finite U]
    [IsProbabilityMeasure μ]
    (hXae : X =ᵐ[μ] X') (hYae : Y =ᵐ[μ] Y') (hZae : Z =ᵐ[μ] Z') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z' ; μ] := by
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype T := Fintype.ofFinite T
  haveI : Fintype U := Fintype.ofFinite U
  exact condMutualInfo_congr_ae
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
    hXae hYae hZae

/-- Conditional mutual information is determined by the joint law of `(X, Y, Z)`: if
`(X, Y, Z)` and `(X', Y', Z')` are identically distributed (possibly on different probability
spaces) then `I(X : Y | Z) = I(X' : Y' | Z')`. See the module docstring for the name clash with
PFR's `ProbabilityTheory.condMutualInfo_eq`.

**Proof sketch.** Expand both sides as `H(X | Z) + H(Y | Z) − H((X, Y) | Z)`. The identical
distribution of the triples transports along the measurable projections to identical
distribution of the pairs `(X, Z)`, `(Y, Z)` and `((X, Y), Z)`, and conditional entropy
depends only on the joint law of the pair (`IdentDistrib.condEntropy_eq`). -/
theorem IdentDistrib.condMutualInfo_eq
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} {Z' : Ω' → U}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    [FiniteRange X'] [FiniteRange Y'] [FiniteRange Z']
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y') (hZ' : Measurable Z')
    (h : IdentDistrib (fun ω => (X ω, Y ω, Z ω))
        (fun ω => (X' ω, Y' ω, Z' ω)) μ μ') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z' ; μ'] := by
  rw [_root_.ProbabilityTheory.condMutualInfo_eq (μ := μ) hX hY hZ,
    _root_.ProbabilityTheory.condMutualInfo_eq (μ := μ') hX' hY' hZ']
  have hXZ :
      IdentDistrib (fun ω => (X ω, Z ω)) (fun ω => (X' ω, Z' ω)) μ μ' :=
    h.comp (Measurable.of_discrete (f := fun a : S × T × U => (a.1, a.2.2)))
  have hYZ :
      IdentDistrib (fun ω => (Y ω, Z ω)) (fun ω => (Y' ω, Z' ω)) μ μ' :=
    h.comp (Measurable.of_discrete (f := fun a : S × T × U => (a.2.1, a.2.2)))
  have hXYZ :
      IdentDistrib (fun ω => ((X ω, Y ω), Z ω))
          (fun ω => ((X' ω, Y' ω), Z' ω)) μ μ' :=
    h.comp (Measurable.of_discrete (f := fun a : S × T × U => ((a.1, a.2.1), a.2.2)))
  rw [IdentDistrib.condEntropy_eq hX hZ hX' hZ' hXZ,
    IdentDistrib.condEntropy_eq hY hZ hY' hZ' hYZ,
    IdentDistrib.condEntropy_eq (hX.prodMk hY) hZ (hX'.prodMk hY') hZ' hXYZ]

/-- If `(X, Y, Z)` and `(X', Y', Z')` are identically distributed on finite measurable sample
spaces with finite alphabets, then `I(X : Y | Z) = I(X' : Y' | Z')`. This is the finite-space
form of `IdentDistrib.condMutualInfo_eq`, which infers measurability from the finite
measurable sample spaces and the finite-range hypotheses from the finite alphabets. -/
theorem IdentDistrib.condMutualInfo_eq_finite
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} {Z' : Ω' → U}
    [CommunicationComplexity.FiniteMeasureSpace Ω]
    [CommunicationComplexity.FiniteMeasureSpace Ω']
    [Finite S] [Finite T] [Finite U]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (h : IdentDistrib (fun ω => (X ω, Y ω, Z ω))
        (fun ω => (X' ω, Y' ω, Z' ω)) μ μ') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z' ; μ'] := by
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype T := Fintype.ofFinite T
  haveI : Fintype U := Fintype.ofFinite U
  exact IdentDistrib.condMutualInfo_eq
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
    h

/-- Conditional mutual information is unchanged by injective recodings of the right variable
and the conditioning variable: for injective `f` and `g`,
`I(X : f(Y) | g(Z)) = I(X : Y | Z)`. [RY20, Ch. 6, Definition (mutual information)]
(invariance under injective recoding, implicit in the definition through the joint
distribution).

**Proof sketch.** Expand both sides as `H(X | ·) + H(· | ·) − H((X, ·) | ·)` (PFR's
`condMutualInfo_eq`) and match the three conditional entropies:
Step 1: `H(X | g(Z)) = H(X | Z)` since `g` is injective.
Step 2: `H(f(Y) | g(Z)) = H(Y | Z)`, stripping first `f` and then `g`.
Step 3: `H((X, f(Y)) | g(Z)) = H((X, Y) | Z)`, since `(x, y) ↦ (x, f(y))` is injective, and
then stripping `g` as before. -/
theorem condMutualInfo_comp_right_conditioning_of_injective
    {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
    [MeasurableSingletonClass V] [MeasurableSingletonClass W]
    [Countable V] [Countable W]
    {f : T → V} {g : U → W}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hfinj : Function.Injective f) (hginj : Function.Injective g) :
    I[X : f ∘ Y | g ∘ Z ; μ] = I[X : Y | Z ; μ] := by
  have hY' : Measurable (f ∘ Y) := hfmeas.comp hY
  have hZ' : Measurable (g ∘ Z) := hgmeas.comp hZ
  rw [_root_.ProbabilityTheory.condMutualInfo_eq (μ := μ) hX hY' hZ',
    _root_.ProbabilityTheory.condMutualInfo_eq (μ := μ) hX hY hZ]
  -- Step 1: strip `g` from the conditioning of `H(X | ·)`
  have hXcond :
      H[X | g ∘ Z ; μ] = H[X | Z ; μ] :=
    condEntropy_of_injective' μ hX hZ g hginj hZ'
  -- Step 2: strip `f` and then `g` from `H(f(Y) | g(Z))`
  have hYcond :
      H[f ∘ Y | g ∘ Z ; μ] = H[Y | Z ; μ] := by
    rw [condEntropy_comp_of_injective μ hY f hfinj]
    exact condEntropy_of_injective' μ hY hZ g hginj hZ'
  -- Step 3: the pair `(X, f(Y))` is an injective recoding of `(X, Y)`; then strip `g`
  have hpaircond :
      H[(fun ω => (X ω, (f ∘ Y) ω)) | g ∘ Z ; μ] =
        H[(fun ω => (X ω, Y ω)) | Z ; μ] := by
    have hrec :
        H[(fun ω => (X ω, (f ∘ Y) ω)) | g ∘ Z ; μ] =
          H[(fun ω => (X ω, Y ω)) | g ∘ Z ; μ] := by
      change
        H[(fun p : S × T => (p.1, f p.2)) ∘ (fun ω => (X ω, Y ω)) |
            g ∘ Z ; μ] =
          H[(fun ω => (X ω, Y ω)) | g ∘ Z ; μ]
      exact condEntropy_comp_of_injective μ (hX.prodMk hY)
        (fun p : S × T => (p.1, f p.2))
        (by
          intro a b h
          exact Prod.ext (Prod.ext_iff.mp h).1 (hfinj (Prod.ext_iff.mp h).2))
    rw [hrec]
    exact condEntropy_of_injective' μ (hX.prodMk hY) hZ g hginj hZ'
  rw [hXcond, hYcond, hpaircond]

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- If `(X, Y)` and `(X', Y')` have the same joint law, then conditioning on the same measurable
event `{Y ∈ s}` / `{Y' ∈ s}` preserves the law of `X` / `X'`: `X` under `μ[|Y ∈ s]` and `X'`
under `μ'[|Y' ∈ s]` are identically distributed. This is the heterogeneous-codomain version of
`ProbabilityTheory.IdentDistrib.cond`.

**Proof sketch.** Almost-everywhere measurability of `X` and `X'` under the conditioned
measures follows from that of the pairs, since conditioning is absolutely continuous. For the
laws, fix a measurable set `t`.
Step 1: the pair maps pull the rectangle `t × s` back to the event `{Y ∈ s} ∩ {X ∈ t}` (and
likewise for the primed pair).
Step 2: by the formula for conditional measure, each conditioned pushforward at `t` equals
`μ(Y ∈ s)⁻¹ · μ({Y ∈ s} ∩ {X ∈ t})`.
Step 3: the conditioning events have equal mass, because the second marginals of the two pairs
agree at `s`.
Step 4: the joint events have equal mass, because the pair laws agree at `t × s`. Rewriting
with Steps 2–4 closes the goal. -/
theorem IdentDistrib.cond_of_pair
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X : Ω → A} {Y : Ω → B} {X' : Ω' → A} {Y' : Ω' → B}
    {s : Set B}
    (hs : MeasurableSet s) (hY : Measurable Y) (hY' : Measurable Y')
    (h : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y' ω)) μ μ') :
    IdentDistrib X X' (μ[|Y ⁻¹' s]) (μ'[|Y' ⁻¹' s]) where
  aemeasurable_fst :=
    (measurable_fst.aemeasurable.comp_aemeasurable h.aemeasurable_fst).mono_ac
      cond_absolutelyContinuous
  aemeasurable_snd :=
    (measurable_fst.aemeasurable.comp_aemeasurable h.aemeasurable_snd).mono_ac
      cond_absolutelyContinuous
  map_eq := by
    ext t ht
    have hXae : AEMeasurable X μ := by
      simpa only [Function.comp_def] using
        measurable_fst.aemeasurable.comp_aemeasurable h.aemeasurable_fst
    have hX'ae : AEMeasurable X' μ' := by
      simpa only [Function.comp_def] using
        measurable_fst.aemeasurable.comp_aemeasurable h.aemeasurable_snd
    -- Step 1: the pair maps pull `t ×ˢ s` back to the event `{Y ∈ s} ∩ {X ∈ t}`
    have hs_pre :
        (fun ω => (X ω, Y ω)) ⁻¹' (t ×ˢ s) = Y ⁻¹' s ∩ X ⁻¹' t ∧
        (fun ω => (X' ω, Y' ω)) ⁻¹' (t ×ˢ s) = Y' ⁻¹' s ∩ X' ⁻¹' t :=
      ⟨(Set.mk_preimage_prod X Y).trans (inter_comm _ _),
        (Set.mk_preimage_prod X' Y').trans (inter_comm _ _)⟩
    -- Step 2: `cond_apply` on both sides
    have hcond_apply :
        Measure.map X (μ[|Y ⁻¹' s]) t = (μ (Y ⁻¹' s))⁻¹ * μ (Y ⁻¹' s ∩ X ⁻¹' t) ∧
        Measure.map X' (μ'[|Y' ⁻¹' s]) t = (μ' (Y' ⁻¹' s))⁻¹ * μ' (Y' ⁻¹' s ∩ X' ⁻¹' t) := by
      constructor
      · rw [map_apply₀ (hXae.mono_ac cond_absolutelyContinuous) ht.nullMeasurableSet,
          cond_apply (hY hs)]
      · rw [map_apply₀ (hX'ae.mono_ac cond_absolutelyContinuous) ht.nullMeasurableSet,
          cond_apply (hY' hs)]
    -- Step 3: the conditioning events have equal mass (`h.map_eq` read at `univ ×ˢ s`,
    -- i.e. the second marginals agree at `s`)
    have hsnd : μ (Y ⁻¹' s) = μ' (Y' ⁻¹' s) := by
      simpa only [
        map_apply₀ (h.comp measurable_snd).aemeasurable_fst hs.nullMeasurableSet,
        map_apply₀ (h.comp measurable_snd).aemeasurable_snd hs.nullMeasurableSet] using
        congr_fun (congr_arg (⇑) (h.comp measurable_snd).map_eq) s
    -- Step 4: the joint events have equal mass (`h.map_eq` read at `t ×ˢ s`)
    have hfst : μ (Y ⁻¹' s ∩ X ⁻¹' t) = μ' (Y' ⁻¹' s ∩ X' ⁻¹' t) := by
      simpa only [
        map_apply₀ h.aemeasurable_fst (ht.prod hs).nullMeasurableSet,
        map_apply₀ h.aemeasurable_snd (ht.prod hs).nullMeasurableSet,
        hs_pre.1, hs_pre.2] using
        congr_fun (congr_arg (⇑) h.map_eq) (t ×ˢ s)
    rw [hcond_apply.1, hcond_apply.2, hsnd, hfst]

end ProbabilityTheory
