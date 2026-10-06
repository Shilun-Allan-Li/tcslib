/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FiniteProbabilitySpace
import PFR.ForMathlib.Entropy.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Entropy: basic bounds and data processing

Bounds and elementary invariance facts for Shannon entropy `H[X ; μ]`, mutual information
`I[X : Y ; μ]` and conditional mutual information `I[X : Y | Z ; μ]`, built on the PFR
project's definitions (natural-logarithm units throughout). This is the first part of the
information-theoretic toolkit used by the randomized lower bound for disjointness in
`TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound`; the chain rules
live in `TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.ChainRules` and the remaining
invariance lemmas in `TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.Conditioning`.

## Main definitions

None (this file only proves lemmas about the PFR notions `H[· ; μ]`, `I[· : · ; μ]` and
`I[· : · | · ; μ]`).

## Main results

- `entropy_le_log_of_card_le`, `entropy_le_nat_mul_log_two_of_card_le_two_pow`: entropy is
  at most the logarithm of the alphabet size (at most `c · log 2` for `2 ^ c` symbols)
- `mutualInfo_le_entropy_left`, `mutualInfo_le_entropy_right`,
  `condMutualInfo_le_condEntropy_left`, `condMutualInfo_le_condEntropy_right`,
  `condMutualInfo_le_entropy_left`, `condMutualInfo_le_entropy_right`: (conditional) mutual
  information is at most the (conditional) entropy of either argument
- `condMutualInfo_comp_left_le_of_comp_conditioning`,
  `condMutualInfo_comp_right_le_of_comp_conditioning`: data processing for conditional
  mutual information when the postprocessing may depend on the conditioning variable
- `mutualInfo_congr_ae`, `mutualInfo_comp_right_of_injective`: mutual information depends
  only on the joint law and is invariant under injective recodings of the right variable
- `mutualInfo_eq_zero_of_ae_eq_const_left`, `mutualInfo_eq_zero_of_ae_eq_const_right`,
  `condMutualInfo_eq_zero_of_ae_eq_const_left`, `condMutualInfo_eq_zero_of_ae_eq_const_right`:
  an almost surely constant argument has zero (conditional) mutual information
- `indepFun_of_measureReal_inter_preimage_singleton_eq_mul`: independence from factorization
  on singletons, for finite alphabets

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

/-- The entropy of a random variable taking values in a finite alphabet of size at most `N` is
at most `log N`. [RY20, Ch. 6, remark after Fact 6.2] ("the uniform distribution has maximum
entropy among all distributions on a set", i.e. `H(X) ≤ log |support|`); stated with the
natural logarithm (PFR convention) rather than `log₂`. -/
theorem entropy_le_log_of_card_le [Fintype S] [Nonempty S] [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) {N : ℕ}
    (hcard : Fintype.card S ≤ N) :
    H[X ; μ] ≤ Real.log N := by
  have hcard_pos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard_cast : (Fintype.card S : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcard
  exact (entropy_le_log_card X μ).trans (Real.log_le_log hcard_pos hcard_cast)

/-- The entropy of a random variable whose alphabet has at most `2 ^ c` elements is at most
`c · log 2`, i.e. at most `c` bits. [RY20, Ch. 6, remark after Fact 6.2] ("the uniform
distribution has maximum entropy among all distributions on a set", i.e. `H(X) ≤ log |support|`);
stated with the natural logarithm (PFR convention), which is why the factor `log 2` appears. -/
theorem entropy_le_nat_mul_log_two_of_card_le_two_pow
    [Fintype S] [Nonempty S] [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) {c : ℕ}
    (hcard : Fintype.card S ≤ 2 ^ c) :
    H[X ; μ] ≤ c * Real.log 2 := by
  simpa [Nat.cast_pow] using entropy_le_log_of_card_le X μ hcard

variable {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-- The mutual information `I(X : Y)` is at most the entropy `H(X)` of the left variable.
[RY20, Ch. 6, Definition (mutual information)] (`0 ≤ I(A:B) ≤ H(A)`). -/
theorem mutualInfo_le_entropy_left
    (hX : Measurable X) (hY : Measurable Y)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] ≤ H[X ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY]
  linarith [condEntropy_nonneg X Y μ]

/-- The mutual information `I(X : Y)` is at most the entropy `H(Y)` of the right variable.
[RY20, Ch. 6, Definition (mutual information)] (`0 ≤ I(A:B) ≤ H(A)`, applied after swapping
the arguments). -/
theorem mutualInfo_le_entropy_right
    (hX : Measurable X) (hY : Measurable Y)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] ≤ H[Y ; μ] := by
  rw [mutualInfo_comm hX hY]
  exact mutualInfo_le_entropy_left hY hX

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T] in
/-- Mutual information is unchanged when both variables are replaced by almost-everywhere equal
variables: if `X = X'` and `Y = Y'` almost surely, then `I(X : Y) = I(X' : Y')`. -/
theorem mutualInfo_congr_ae
    {X' : Ω → S} {Y' : Ω → T}
    (hX : Measurable X) (hY : Measurable Y)
    (hXae : X =ᵐ[μ] X') (hYae : Y =ᵐ[μ] Y') :
    I[X : Y ; μ] = I[X' : Y' ; μ] := by
  exact ProbabilityTheory.IdentDistrib.mutualInfo_eq
    (IdentDistrib.of_ae_eq (hX.prodMk hY).aemeasurable (hXae.prodMk hYae))

open Classical in
/-- Mutual information is unchanged by an injective recoding of the right variable: for
injective `f`, `I(X : f(Y)) = I(X : Y)`. [RY20, Ch. 6, Definition (mutual information)]
(invariance under injective recoding, implicit in the definition through the joint
distribution). -/
theorem mutualInfo_comp_right_of_injective
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y)
    (f : T → V) (hf : Measurable f) (hfinj : Function.Injective f) :
    I[X : f ∘ Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hf.comp hY),
    mutualInfo_eq_entropy_sub_condEntropy hX hY]
  rw [condEntropy_of_injective' μ hX hY f hfinj (hf.comp hY)]

omit [Countable S] [Countable T] in
/-- If the left variable is almost surely constant, its mutual information with any finite
variable is zero. -/
theorem mutualInfo_eq_zero_of_ae_eq_const_left
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) (c : S)
    (hconst : X =ᵐ[μ] fun _ => c) :
    I[X : Y ; μ] = 0 := by
  have hindepConst : (fun _ : Ω => c) ⟂ᵢ[μ] Y :=
    indepFun_const_left c Y
  have hindep : X ⟂ᵢ[μ] Y :=
    IndepFun.congr hindepConst hconst.symm (by rfl)
  exact hindep.mutualInfo_eq_zero hX hY

/-- If the right variable is almost surely constant, its mutual information with any finite
variable is zero. -/
theorem mutualInfo_eq_zero_of_ae_eq_const_right
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) (c : T)
    (hconst : Y =ᵐ[μ] fun _ => c) :
    I[X : Y ; μ] = 0 := by
  rw [mutualInfo_comm hX hY]
  exact mutualInfo_eq_zero_of_ae_eq_const_left hY hX c hconst

omit [Countable S] [Countable T] in
open Classical in
/-- If the left variable is almost surely constant, its conditional mutual information with any
finite variable is zero. -/
theorem condMutualInfo_eq_zero_of_ae_eq_const_left
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (c : S)
    (hconst : X =ᵐ[μ] fun _ => c) :
    I[X : Y | Z ; μ] = 0 := by
  apply (condMutualInfo_eq_zero hX hY).mpr
  rw [condIndepFun_iff, ae_iff_of_countable]
  intro z _hz
  have hconst_cond : X =ᵐ[μ[|Z ⁻¹' {z}]] fun _ => c :=
    cond_absolutelyContinuous.ae_le hconst
  exact IndepFun.congr (indepFun_const_left c Y)
    (Filter.EventuallyEq.symm hconst_cond) (by rfl)

/-- If the right variable is almost surely constant, its conditional mutual information with any
finite variable is zero. -/
theorem condMutualInfo_eq_zero_of_ae_eq_const_right
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (c : T)
    (hconst : Y =ᵐ[μ] fun _ => c) :
    I[X : Y | Z ; μ] = 0 := by
  rw [condMutualInfo_comm hX hY Z μ]
  exact condMutualInfo_eq_zero_of_ae_eq_const_left hY hX c hconst

open Classical in
/-- For finite alphabets, independence of two random variables follows from factorization on
singleton fibers: if `μ(X = x, Y = y) = μ(X = x) · μ(Y = y)` for all `x`, `y`, then `X` and `Y`
are independent.

**Proof sketch.** Independence is the statement that the law of the pair `(X, Y)` is the
product of the marginal laws; on a finite product alphabet two finite measures agree once they
agree on singletons. For a singleton `{(x, y)}` the pushforward of the pair is
`μ({X = x} ∩ {Y = y})`, which factorises by hypothesis, while the product measure of
`{x} ×ˢ {y}` is `μ(X = x) · μ(Y = y)`. -/
theorem indepFun_of_measureReal_inter_preimage_singleton_eq_mul
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [Finite S] [Finite T] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → S) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ x y,
      μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) =
        μ.real (X ⁻¹' {x}) * μ.real (Y ⁻¹' {y})) :
    IndepFun X Y μ := by
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype T := Fintype.ofFinite T
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
  rw [Measure.ext_iff_measureReal_singleton_finiteSupport]
  rintro ⟨x, y⟩
  rw [MeasureTheory.map_measureReal_apply (hX.prodMk hY) MeasurableSet.of_discrete]
  rw [show (fun ω => (X ω, Y ω)) ⁻¹' ({(x, y)} : Set (S × T)) =
      X ⁻¹' ({x} : Set S) ∩ Y ⁻¹' ({y} : Set T) by
    ext ω
    simp [Prod.ext_iff]]
  rw [h x y]
  rw [show ({(x, y)} : Set (S × T)) = ({x} : Set S) ×ˢ ({y} : Set T) by
    ext z
    simp [Prod.ext_iff]]
  rw [MeasureTheory.measureReal_prod_prod]
  rw [MeasureTheory.map_measureReal_apply hX MeasurableSet.of_discrete]
  rw [MeasureTheory.map_measureReal_apply hY MeasurableSet.of_discrete]

/-- The conditional mutual information `I(X : Y | Z)` is at most the conditional entropy
`H(X | Z)` of the left variable. [RY20, Ch. 6, Definition (mutual information)]
(`0 ≤ I(A:B) ≤ H(A)`, conditional form). -/
theorem condMutualInfo_le_condEntropy_left
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[X | Z ; μ] := by
  rw [condMutualInfo_eq' hX hY hZ]
  linarith [condEntropy_nonneg X (fun ω => (Y ω, Z ω)) μ]

/-- The conditional mutual information `I(X : Y | Z)` is at most the conditional entropy
`H(Y | Z)` of the right variable. [RY20, Ch. 6, Definition (mutual information)]
(`0 ≤ I(A:B) ≤ H(A)`, conditional form). -/
theorem condMutualInfo_le_condEntropy_right
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[Y | Z ; μ] := by
  rw [condMutualInfo_comm hX hY Z μ]
  exact condMutualInfo_le_condEntropy_left hY hX hZ

/-- The conditional mutual information `I(X : Y | Z)` is at most the (unconditional) entropy
`H(X)` of the left variable. [RY20, Ch. 6, Definition (mutual information)]
(`0 ≤ I(A:B) ≤ H(A)`, combined with `H(X | Z) ≤ H(X)`). -/
theorem condMutualInfo_le_entropy_left
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[X ; μ] :=
  (condMutualInfo_le_condEntropy_left hX hY hZ).trans
    (condEntropy_le_entropy μ hX hZ)

/-- The conditional mutual information `I(X : Y | Z)` is at most the (unconditional) entropy
`H(Y)` of the right variable. [RY20, Ch. 6, Definition (mutual information)]
(`0 ≤ I(A:B) ≤ H(A)`, combined with `H(Y | Z) ≤ H(Y)`). -/
theorem condMutualInfo_le_entropy_right
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[Y ; μ] :=
  (condMutualInfo_le_condEntropy_right hX hY hZ).trans
    (condEntropy_le_entropy μ hY hZ)

/-- Conditional data processing where the left-side postprocessing may depend on the
conditioning value: for any function `f`, `I(f(Z, X) : Y | Z) ≤ I(X : Y | Z)`.
[RY20, Ch. 6, §Subadditivity] (data processing / conditioning monotonicity). -/
theorem condMutualInfo_comp_left_le_of_comp_conditioning
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : U → S → V) :
    I[fun ω => f (Z ω) (X ω) : Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hZX :
      I[fun ω => (Z ω, X ω) : Y | Z ; μ] = I[X : Y | Z ; μ] :=
    condMutualInfo_of_inj_map hX hY hZ
      (fun z x => (z, x)) (fun _ _ _ h => (Prod.ext_iff.1 h).2)
  have hle :
      I[fun ω => f (Z ω) (X ω) : Y | Z ; μ] ≤
        I[fun ω => (Z ω, X ω) : Y | Z ; μ] := by
    simpa [Function.comp_def] using
      condMutual_comp_comp_le (μ := μ)
        (X := fun ω => (Z ω, X ω)) (Y := Y) (Z := Z)
        (hX := hZ.prodMk hX) (hY := hY) (hZ := hZ)
        (f := fun zx => f zx.1 zx.2) (g := id) measurable_id
  exact hle.trans_eq hZX

/-- Conditional data processing where the right-side postprocessing may depend on the
conditioning value: for any measurable `f`, `I(X : f(Z, Y) | Z) ≤ I(X : Y | Z)`.
[RY20, Ch. 6, §Subadditivity] (data processing / conditioning monotonicity). -/
theorem condMutualInfo_comp_right_le_of_comp_conditioning
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : U → T → V) (hf : Measurable (Function.uncurry f)) :
    I[X : (fun ω => f (Z ω) (Y ω)) | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hfZY : Measurable (fun ω => f (Z ω) (Y ω)) :=
    hf.comp (hZ.prodMk hY)
  rw [condMutualInfo_comm hX hfZY Z μ, condMutualInfo_comm hX hY Z μ]
  exact condMutualInfo_comp_left_le_of_comp_conditioning
    (μ := μ) (X := Y) (Y := X) (Z := Z)
    hY hX hZ f

end ProbabilityTheory
