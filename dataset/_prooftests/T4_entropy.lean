import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.ConditionalProbability
import PFR.ForMathlib.Entropy.Basic

namespace ProbabilityTheory
end ProbabilityTheory

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open ProbabilityTheory
open MeasureTheory Measure Set

namespace ProbabilityTheory
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
variable {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
omit [Countable S] [Countable T] in
open Classical in
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
end ProbabilityTheory

namespace ProbabilityTheory
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
variable {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  {W : Ω → V}
theorem condMutualInfo_prod_left_eq_add
    (hX : Measurable X) (hW : Measurable W) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange W] [FiniteRange Y]
    [FiniteRange Z] :
    I[fun ω => (X ω, W ω) : Y | Z ; μ] =
      I[X : Y | Z ; μ] + I[W : Y | fun ω => (X ω, Z ω) ; μ] := by
  have hA :
      H[W | (fun ω => (X ω, (Y ω, Z ω))) ; μ] =
        H[W | (fun ω => (Y ω, (X ω, Z ω))) ; μ] := by
    let f : T × (S × U) → S × (T × U) := fun t => (t.2.1, (t.1, t.2.2))
    have hf : Function.Injective f := by
      intro a b h
      rcases a with ⟨aY, aX, aZ⟩
      rcases b with ⟨bY, bX, bZ⟩
      simp only [f, Prod.mk.injEq] at h ⊢
      exact ⟨h.2.1, h.1, h.2.2⟩
    have hf_meas : Measurable f := Measurable.of_discrete
    have hfY : Measurable (f ∘ fun ω => (Y ω, (X ω, Z ω))) :=
      hf_meas.comp (hY.prodMk (hX.prodMk hZ))
    simpa [f, Function.comp_def] using
      (condEntropy_of_injective' μ hW (hY.prodMk (hX.prodMk hZ)) f hf
        hfY)
  rw [condMutualInfo_eq' (hX.prodMk hW) hY hZ,
    condMutualInfo_eq' hX hY hZ,
    condMutualInfo_eq' hW hY (hX.prodMk hZ),
    cond_chain_rule' μ hX hW hZ,
    cond_chain_rule' μ hX hW (hY.prodMk hZ),
    hA]
  ring
end ProbabilityTheory

namespace ProbabilityTheory
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
variable {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  {W : Ω → V}
def boolVectorStrictPrefix {Ω : Type*} {m : ℕ}
    (X : Ω → Fin m → Bool) (i : Fin m) (ω : Ω) : Fin i.1 → Bool :=
  fun j => X ω ⟨j.1, lt_trans j.2 i.2⟩
end ProbabilityTheory

namespace ProbabilityTheory
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
variable {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  {W : Ω → V}
open Classical in
theorem condMutualInfo_boolVector_eq_sum_strictPrefix
    {Ω T U : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSingletonClass T] [MeasurableSingletonClass U] [Countable T] [Countable U]
    {m : ℕ} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange Y] [FiniteRange Z]
    (X : Ω → Fin m → Bool)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[X : Y | Z ; μ] =
      ∑ i : Fin m,
        I[(fun ω => X ω i) : Y | (fun ω => (boolVectorStrictPrefix X i ω, Z ω)) ; μ] := by
  induction m with
  | zero =>
      have hconst : X =ᵐ[μ] fun _ => (Fin.elim0 : Fin 0 → Bool) := by
        filter_upwards with ω
        funext i
        exact Fin.elim0 i
      rw [Fin.sum_univ_zero]
      exact ProbabilityTheory.condMutualInfo_eq_zero_of_ae_eq_const_left
        hX hY (Fin.elim0 : Fin 0 → Bool) hconst
  | succ m ih =>
      let Xinit : Ω → Fin m → Bool := fun ω i => X ω i.castSucc
      let Xlast : Ω → Bool := fun ω => X ω (Fin.last m)
      have hXinit : Measurable Xinit := by
        rw [measurable_pi_iff]
        intro i
        exact (measurable_pi_apply i.castSucc).comp hX
      have hXlast : Measurable Xlast :=
        (measurable_pi_apply (Fin.last m)).comp hX
      let splitLast : (Fin (m + 1) → Bool) → (Fin m → Bool) × Bool :=
        fun v => (fun i => v i.castSucc, v (Fin.last m))
      have hsplitLast_inj : Function.Injective splitLast := by
        intro a b h
        funext k
        cases k using Fin.lastCases with
        | last =>
            exact congrArg Prod.snd h
        | cast i =>
            exact congr_fun (congrArg Prod.fst h) i
      have hsplit :
          I[(fun ω => (Xinit ω, Xlast ω)) : Y | Z ; μ] = I[X : Y | Z ; μ] := by
        simpa [splitLast, Xinit, Xlast, Function.comp_def] using
          ProbabilityTheory.condMutualInfo_of_inj_map
            (μ := μ) (X := X) (Y := Y) (Z := Z)
            hX hY hZ (fun _ v => splitLast v) (fun _ => hsplitLast_inj)
      rw [← hsplit]
      rw [ProbabilityTheory.condMutualInfo_prod_left_eq_add hXinit hXlast hY hZ]
      rw [ih Xinit hXinit]
      rw [Fin.sum_univ_castSucc]
      congr 1
end ProbabilityTheory
