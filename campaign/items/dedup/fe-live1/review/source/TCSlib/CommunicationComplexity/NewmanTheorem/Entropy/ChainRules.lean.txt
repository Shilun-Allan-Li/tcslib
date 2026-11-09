/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Entropy: chain rules and fiber decompositions

Chain rules and conditioning-monotonicity lemmas for mutual information `I[X : Y ; μ]` and
conditional mutual information `I[X : Y | Z ; μ]`, built on the PFR project's definitions
(natural-logarithm units throughout). This is the second part of the information-theoretic
toolkit used by the randomized lower bound for disjointness in
`TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound`; the basic bounds
are in `TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.Basic` and the invariance
lemmas in `TCSlib.CommunicationComplexity.NewmanTheorem.Entropy.Conditioning`.

## Main definitions

- `boolVectorStrictPrefix`: the strict prefix `(X₀, …, X_{i-1})` of a boolean-vector-valued
  random variable `X : Ω → Fin m → Bool`

## Main results

- `condMutualInfo_prod_left_eq_add`, `condMutualInfo_prod_right_eq_add`,
  `mutualInfo_prod_right_eq_add`: chain rules for (conditional) mutual information
- `condMutualInfo_boolVector_eq_sum_strictPrefix`: the iterated chain rule over the
  coordinates of a boolean vector
- `condMutualInfo_prod_conditioning_eq_sum`,
  `measureReal_mul_cond_condMutualInfo_le_condMutualInfo_of_event_eq_preimage`: conditional
  mutual information given `(K, Z)` as a mass-weighted average over the fibers of `K`, and
  the lower bound `μ(A) · I(X : Y | Z ; μ[|A]) ≤ I(X : Y | Z ; μ)` for an event `A`
  determined by `Z`
- `condMutualInfo_conditioning_prod_left_function_le`,
  `condMutualInfo_conditioning_prod_right_function_le`,
  `condMutualInfo_comp_conditioning_le_of_condMutualInfo_eq_zero`,
  `condMutualInfo_le_mutualInfo_of_condDependence_le`: data processing and monotonicity of
  conditional mutual information under coarsening or refining the conditioning
- `cond_cond_eq_cond_of_subset`, `measureReal_mul_cond_real_eq_measureReal_of_subset`:
  nested conditioning of a measure on a smaller event

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

/-- Adding a deterministic function of the conditioning variable to the conditioning variable does
not change conditional mutual information. -/
theorem condMutualInfo_conditioning_prod_function_eq
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (f : U → V) :
    I[X : Y | (fun ω => (Z ω, f (Z ω))) ; μ] = I[X : Y | Z ; μ] := by
  simpa [Function.comp_def] using
    condMutualInfo_of_inj hX hY hZ μ
      (f := fun z => (z, f z)) (fun _ _ h => (Prod.ext_iff.1 h).1)

open Classical in
/-- Conditioning additionally on a deterministic function of the left variable and the existing
conditioning data cannot increase conditional mutual information:
`I(X : Y | (Z, f(Z, X))) ≤ I(X : Y | Z)`. [RY20, Ch. 6, §Subadditivity] (data processing /
conditioning monotonicity).

**Proof sketch.** Write `A = (Z, f(Z, X))` for the refined conditioning variable.
Step 1: `Z` is a function of `A` (the first projection), so `H(Y | A) ≤ H(Y | Z)`.
Step 2: the pair `(X, A)` is an injective recoding of `(X, Z)`, so `H(Y | X, A) = H(Y | X, Z)`.
Step 3: swap the two arguments of both conditional mutual informations and expand them as
`I(Y : X | ·) = H(Y | ·) − H(Y | X, ·)`; the inequality then follows from Steps 1 and 2 by
linear arithmetic. -/
theorem condMutualInfo_conditioning_prod_left_function_le
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : U → S → V) (hf : Measurable (Function.uncurry f)) :
    I[X : Y | (fun ω => (Z ω, f (Z ω) (X ω))) ; μ] ≤
      I[X : Y | Z ; μ] := by
  let A : Ω → U × V := fun ω => (Z ω, f (Z ω) (X ω))
  let XZ : Ω → S × U := fun ω => (X ω, Z ω)
  let recode : S × U → S × (U × V) := fun xu => (xu.1, (xu.2, f xu.2 xu.1))
  have hA : Measurable A := by
    exact hZ.prodMk (hf.comp (hZ.prodMk hX))
  haveI : FiniteRange (fun ω => f (Z ω) (X ω)) := by
    change FiniteRange (Function.uncurry f ∘ fun ω => (Z ω, X ω))
    infer_instance
  haveI : FiniteRange A := by
    dsimp only [A]
    infer_instance
  haveI : FiniteRange XZ := by
    dsimp only [XZ]
    infer_instance
  -- Step 1: `Z` is a function of `A`, so conditioning on `A` lowers the entropy of `Y`
  have hfirst : H[Y | A ; μ] ≤ H[Y | Z ; μ] := by
    have hge :=
      condEntropy_comp_ge (μ := μ) (X := A) (Y := Y)
        hA hY (fun a : U × V => a.1)
    simpa [A, Function.comp_def] using hge
  -- Step 2: `(X, A)` is an injective recoding of `(X, Z)`
  have hrec_inj : Function.Injective recode := by
    intro a b h
    exact Prod.ext (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 (Prod.ext_iff.1 h).2).1
  have hrec_meas : Measurable (recode ∘ XZ) := by
    simpa [recode, XZ, A, Function.comp_def] using hX.prodMk hA
  have hsecond :
      H[Y | (fun ω => (X ω, A ω)) ; μ] = H[Y | XZ ; μ] := by
    simpa [recode, XZ, A, Function.comp_def] using
      condEntropy_of_injective' μ hY (hX.prodMk hZ) recode hrec_inj hrec_meas
  -- Step 3: swap the arguments, expand as `H(Y | ·) − H(Y | X, ·)`, and combine
  rw [condMutualInfo_comm hX hY A μ, condMutualInfo_comm hX hY Z μ,
    condMutualInfo_eq' hY hX hA μ, condMutualInfo_eq' hY hX hZ μ]
  rw [hsecond]
  linarith

open Classical in
/-- Conditioning additionally on a deterministic function of the right variable and the existing
conditioning data cannot increase conditional mutual information:
`I(X : Y | (Z, f(Z, Y))) ≤ I(X : Y | Z)`. [RY20, Ch. 6, §Subadditivity] (data processing /
conditioning monotonicity). -/
theorem condMutualInfo_conditioning_prod_right_function_le
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : U → T → V) (hf : Measurable (Function.uncurry f)) :
    I[X : Y | (fun ω => (Z ω, f (Z ω) (Y ω))) ; μ] ≤
      I[X : Y | Z ; μ] := by
  rw [condMutualInfo_comm hX hY (fun ω => (Z ω, f (Z ω) (Y ω))) μ,
    condMutualInfo_comm hX hY Z μ]
  exact condMutualInfo_conditioning_prod_left_function_le
    (μ := μ) (X := Y) (Y := X) (Z := Z) hY hX hZ f hf

/-- If a coarse conditioning variable `f(W)` is a deterministic function of a finer one `W`, and
the finer conditioning variable carries no conditional information about `X` beyond the coarse
variable (`I(X : W | f(W)) = 0`), then refining the conditioning can only increase the
conditional mutual information: `I(X : Y | f(W)) ≤ I(X : Y | W)`.
[RY20, Ch. 6, §Subadditivity] (data processing / conditioning monotonicity).

**Proof sketch.** Write `Z = f(W)`.
Step 1: `(W, Z)` is an injective recoding of `W`, so `H(X | W, Z) = H(X | W)`.
Step 2: expanding the hypothesis `I(X : W | Z) = H(X | Z) − H(X | W, Z) = 0` and using
Step 1 gives `H(X | Z) = H(X | W)`.
Step 3: `(Y, Z)` is a function of `(Y, W)`, so `H(X | Y, W) ≤ H(X | Y, Z)`.
Step 4: expand both sides as `I(X : Y | ·) = H(X | ·) − H(X | Y, ·)` and combine Steps 2
and 3 by linear arithmetic. -/
theorem condMutualInfo_comp_conditioning_le_of_condMutualInfo_eq_zero
    {W : Ω → V} (f : V → U)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange W]
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hf : Measurable f)
    (hzero : I[X : W|f ∘ W;μ] = 0) :
    I[X : Y|f ∘ W;μ] ≤ I[X : Y|W;μ] := by
  let Z : Ω → U := f ∘ W
  have hZ : Measurable Z := hf.comp hW
  -- Step 1: `(W, Z)` is an injective recoding of `W`
  have hWZ :
      H[X | (fun ω => (W ω, Z ω)) ; μ] = H[X | W ; μ] := by
    let g : V → V × U := fun w => (w, f w)
    have hg : Function.Injective g := fun a b h => (Prod.ext_iff.1 h).1
    have hgW : Measurable (g ∘ W) := Measurable.of_discrete.comp hW
    simpa [g, Z, Function.comp_def] using
      condEntropy_of_injective' μ hX hW g hg hgW
  -- Step 2: the vanishing conditional information gives `H(X | Z) = H(X | W)`
  have hfirst : H[X | Z ; μ] = H[X | W ; μ] := by
    have hzero' : I[X : W | Z ; μ] = 0 := by
      simpa [Z] using hzero
    rw [condMutualInfo_eq' hX hW hZ μ, hWZ] at hzero'
    linarith
  -- Step 3: `(Y, Z)` is a function of `(Y, W)`
  have hsecond :
      H[X | (fun ω => (Y ω, W ω)) ; μ] ≤
        H[X | (fun ω => (Y ω, Z ω)) ; μ] := by
    let g : T × V → T × U := fun yw => (yw.1, f yw.2)
    have hg : Measurable g := Measurable.of_discrete
    simpa [g, Z, Function.comp_def] using
      condEntropy_comp_ge (μ := μ)
        (X := fun ω => (Y ω, W ω)) (Y := X)
        (hX := hY.prodMk hW) (hY := hX) g
  -- Step 4: expand both conditional mutual informations and combine
  have hmain : I[X : Y | Z ; μ] ≤ I[X : Y | W ; μ] := by
    rw [condMutualInfo_eq' hX hY hZ μ,
      condMutualInfo_eq' hX hY hW μ]
    linarith
  simpa [Z, Function.comp_def] using hmain

/-- Chain rule for conditional mutual information, splitting a pair on the left:
`I((X, W) : Y | Z) = I(X : Y | Z) + I(W : Y | (X, Z))`. [RY20, Ch. 6, §Chain Rules] (chain
rule for (conditional) mutual information, `I(AB:C) = I(A:C) + I(B:C|A)`, here with an extra
conditioning variable throughout).

**Proof sketch.** Step 1: permuting the coordinates of the conditioning triple is injective, so
`H(W | X, (Y, Z)) = H(W | Y, (X, Z))`. Step 2: expand each of the three conditional mutual
informations as `H(· | Z) − H(· | Y, Z)`, expand `H((X, W) | Z)` and `H((X, W) | Y, Z)` by the
chain rule for conditional entropy, substitute Step 1, and close by `ring`. -/
theorem condMutualInfo_prod_left_eq_add
    (hX : Measurable X) (hW : Measurable W) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange W] [FiniteRange Y]
    [FiniteRange Z] :
    I[fun ω => (X ω, W ω) : Y | Z ; μ] =
      I[X : Y | Z ; μ] + I[W : Y | fun ω => (X ω, Z ω) ; μ] := by
  -- Step 1: reorder the conditioning triple (an injective recoding)
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
  -- Step 2: expand as conditional entropies, apply the entropy chain rule, and close by `ring`
  rw [condMutualInfo_eq' (hX.prodMk hW) hY hZ,
    condMutualInfo_eq' hX hY hZ,
    condMutualInfo_eq' hW hY (hX.prodMk hZ),
    cond_chain_rule' μ hX hW hZ,
    cond_chain_rule' μ hX hW (hY.prodMk hZ),
    hA]
  ring

/-- Chain rule for conditional mutual information, splitting a pair on the right:
`I(X : (Y, W) | Z) = I(X : Y | Z) + I(X : W | (Y, Z))`. [RY20, Ch. 6, §Chain Rules] (chain rule
for (conditional) mutual information); obtained from `condMutualInfo_prod_left_eq_add` by
symmetry. -/
theorem condMutualInfo_prod_right_eq_add
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange W]
    [FiniteRange Z] :
    I[X : (fun ω => (Y ω, W ω)) | Z ; μ] =
      I[X : Y | Z ; μ] + I[X : W | fun ω => (Y ω, Z ω) ; μ] := by
  rw [condMutualInfo_comm hX (hY.prodMk hW) Z μ,
    condMutualInfo_prod_left_eq_add hY hW hX hZ,
    condMutualInfo_comm hY hX Z μ,
    condMutualInfo_comm hW hX (fun ω => (Y ω, Z ω)) μ]

omit [Countable U] in
/-- Adding an extra right-side variable cannot decrease conditional mutual information:
`I(X : W | Z) ≤ I(X : (Y, W) | Z)`. [RY20, Ch. 6, §Subadditivity] (data processing: `W` is the
second projection of `(Y, W)`). -/
theorem condMutualInfo_le_prod_right_snd
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hZ : Measurable Z)
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange W]
    [FiniteRange Z] :
    I[X : W | Z ; μ] ≤ I[X : (fun ω => (Y ω, W ω)) | Z ; μ] := by
  simpa [Function.comp_def] using
    condMutual_comp_comp_le (μ := μ)
      (X := X) (Y := fun ω => (Y ω, W ω)) (Z := Z)
      hX (hY.prodMk hW) hZ (fun x : S => x) Prod.snd Measurable.of_discrete

/-- The strict prefix of a boolean vector-valued random variable: for `X : Ω → Fin m → Bool`
and `i : Fin m`, the random variable `ω ↦ (X ω 0, …, X ω (i - 1))` recording the coordinates
strictly before `i`. -/
def boolVectorStrictPrefix {Ω : Type*} {m : ℕ}
    (X : Ω → Fin m → Bool) (i : Fin m) (ω : Ω) : Fin i.1 → Bool :=
  fun j => X ω ⟨j.1, lt_trans j.2 i.2⟩

open Classical in
/-- Chain rule for conditional mutual information against a finite boolean vector, exposing
coordinates from left to right: for `X = (X₀, …, X_{m-1})`,
`I(X : Y | Z) = Σᵢ I(Xᵢ : Y | (X_{<i}, Z))`, where `X_{<i}` is the strict prefix.
[RY20, Lemma 6.15 proof] (iterated chain rule over coordinates).

**Proof sketch.** Induction on the length `m`.
Step 1 (base case): a vector of length `0` is almost surely the constant empty vector, so the
conditional mutual information vanishes and both sides are `0`.
Step 2 (inductive step): split `X` into its first `m` coordinates `Xinit` and its last
coordinate `Xlast`; the map `v ↦ (init v, last v)` is injective, so
`I((Xinit, Xlast) : Y | Z) = I(X : Y | Z)`.
Step 3: apply the two-variable chain rule `condMutualInfo_prod_left_eq_add` to get
`I(Xinit : Y | Z) + I(Xlast : Y | (Xinit, Z))`, rewrite the first summand by the induction
hypothesis, and match the resulting sum with `Fin.sum_univ_castSucc`. -/
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
      -- Step 1: the empty vector is constant, so the information is zero
      have hconst : X =ᵐ[μ] fun _ => (Fin.elim0 : Fin 0 → Bool) := by
        filter_upwards with ω
        funext i
        exact Fin.elim0 i
      rw [Fin.sum_univ_zero]
      exact ProbabilityTheory.condMutualInfo_eq_zero_of_ae_eq_const_left
        hX hY (Fin.elim0 : Fin 0 → Bool) hconst
  | succ m ih =>
      -- Step 2: split off the last coordinate by an injective recoding
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
      -- Step 3: two-variable chain rule, induction hypothesis, and reindexing of the sum
      rw [← hsplit]
      rw [ProbabilityTheory.condMutualInfo_prod_left_eq_add hXinit hXlast hY hZ]
      rw [ih Xinit hXinit]
      rw [Fin.sum_univ_castSucc]
      congr 1

open Classical in
/-- Conditioning on a larger event and then on a smaller event is the same as conditioning
directly on the smaller event. -/
theorem cond_cond_eq_cond_of_subset
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (μ : Measure Ω₀) [IsFiniteMeasure μ]
    {A F : Set Ω₀} (hA : MeasurableSet A) (hF : MeasurableSet F) (hFA : F ⊆ A) :
    μ[|A][|F] = μ[|F] := by
  rw [ProbabilityTheory.cond_cond_eq_cond_inter hA hF μ]
  rw [Set.inter_eq_right.mpr hFA]

open Classical in
/-- Real masses obey the same reweighting identity for nested conditioning events. -/
theorem measureReal_mul_cond_real_eq_measureReal_of_subset
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (μ : Measure Ω₀) [IsFiniteMeasure μ]
    {A F : Set Ω₀} (hA : MeasurableSet A) (hFA : F ⊆ A) :
    μ.real A * (μ[|A]).real F = μ.real F := by
  rw [ProbabilityTheory.cond_real_apply hA]
  rw [Set.inter_eq_right.mpr hFA]
  by_cases hmass : μ.real A = 0
  · have hFmass : μ.real F = 0 := by
      have hle : μ.real F ≤ μ.real A := measureReal_mono hFA
      have hnonneg : 0 ≤ μ.real F := measureReal_nonneg
      linarith
    simp [hmass, hFmass]
  · field_simp [hmass]

open Classical in
/-- If the conditioning variable is a pair `(K, Z)`, conditional mutual information is the
average over the fibers of `K` of the conditional mutual information given `Z`:
`I(X : Y | (K, Z) ; μ) = Σ_k μ(K = k) · I(X : Y | Z ; μ[|K = k])`.
[RY20, Ch. 6, §Chain Rules] (conditional mutual information as an average over fibers of the
conditioning variable; the textbook takes this as the definition of the conditional quantity).

**Proof sketch.** Step 1: expand both sides by `condMutualInfo_eq_sum'`, which writes a
conditional mutual information as the sum over the values of the conditioning variable of the
mass of the fiber times the mutual information under the measure conditioned on that fiber;
on the left the sum runs over pairs `(k, z)`, on the right over `k` and then `z` once the mass
`μ(K = k)` is distributed into the inner sum.
Step 2: compare the summands for a fixed `(k, z)`. The `(K, Z)`-fiber of `(k, z)` is the
intersection `{K = k} ∩ {Z = z}`; the masses satisfy
`μ(K = k) · μ[|K = k](Z = z) = μ({K = k} ∩ {Z = z})` (nested-conditioning identity,
`measureReal_mul_cond_real_eq_measureReal_of_subset`); and iterated conditioning equals
conditioning on the intersection (`cond_cond_eq_cond_inter`). Substituting and closing by
`ring` finishes the proof. -/
theorem condMutualInfo_prod_conditioning_eq_sum
    {Ω₀ S₀ T₀ A U₀ : Type*}
    [MeasurableSpace Ω₀] [MeasurableSpace S₀] [MeasurableSpace T₀]
    [MeasurableSpace A] [MeasurableSpace U₀]
    [MeasurableSingletonClass S₀] [MeasurableSingletonClass T₀]
    [MeasurableSingletonClass A] [MeasurableSingletonClass U₀]
    [Countable S₀] [Countable T₀] [Fintype A] [Finite U₀]
    {X : Ω₀ → S₀} {Y : Ω₀ → T₀} {K : Ω₀ → A} {Z : Ω₀ → U₀}
    {μ : Measure Ω₀} [IsFiniteMeasure μ]
    (hK : Measurable K) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] :
    I[X : Y | (fun ω => (K ω, Z ω)) ; μ] =
      ∑ k : A, μ.real (K ⁻¹' {k}) * I[X : Y | Z ; μ[|K ← k]] := by
  letI := Fintype.ofFinite U₀
  -- Step 1: expand both sides as fiber sums and reindex the left sum over pairs
  rw [ProbabilityTheory.condMutualInfo_eq_sum'
    (μ := μ) (X := X) (Y := Y) (Z := fun ω => (K ω, Z ω)) (hK.prodMk hZ)]
  simp_rw [ProbabilityTheory.condMutualInfo_eq_sum'
    (X := X) (Y := Y) (Z := Z) hZ]
  simp_rw [Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro z _hz
  -- Step 2: for fixed `(k, z)`, identify the pair fiber, its mass and the iterated conditioning
  let Aset : Set Ω₀ := K ⁻¹' ({k} : Set A)
  let Zset : Set Ω₀ := Z ⁻¹' ({z} : Set U₀)
  have hAmeas : MeasurableSet Aset := hK MeasurableSet.of_discrete
  have hZmeas : MeasurableSet Zset := hZ MeasurableSet.of_discrete
  have hpair :
      (fun ω => (K ω, Z ω)) ⁻¹' ({(k, z)} : Set (A × U₀)) = Aset ∩ Zset := by
    ext ω
    simp [Aset, Zset, Prod.ext_iff]
  have hmass :
      μ.real Aset * (μ[|K ← k]).real Zset = μ.real (Aset ∩ Zset) := by
    have hsupport :
        (μ[|K ← k]).real Zset = (μ[|K ← k]).real (Aset ∩ Zset) := by
      have hset : Aset ∩ Zset = Aset ∩ (Aset ∩ Zset) := by
        ext ω
        simp
      rw [ProbabilityTheory.cond_real_apply hAmeas,
        ProbabilityTheory.cond_real_apply hAmeas]
      exact congrArg (fun s : Set Ω₀ => (μ.real Aset)⁻¹ * μ.real s) hset
    rw [hsupport]
    exact ProbabilityTheory.measureReal_mul_cond_real_eq_measureReal_of_subset
      μ hAmeas Set.inter_subset_left
  have hcond :
      μ[|K ← k][|Z ← z] = μ[|Aset ∩ Zset] := by
    rw [ProbabilityTheory.cond_cond_eq_cond_inter hAmeas hZmeas]
  rw [hpair, hcond]
  rw [← hmass]
  ring

open Classical in
/-- If an event `A = {Z ∈ B}` is determined by the conditioning variable, then the contribution
of the conditional mutual information on that event is bounded by the original conditional
mutual information: `μ(A) · I(X : Y | Z ; μ[|A]) ≤ I(X : Y | Z ; μ)`.
[RY20, Ch. 6, §Chain Rules] (conditional mutual information as an average over fibers of the
conditioning variable: the fibers inside `A` contribute a part of the full average, and every
contribution is nonnegative).

**Proof sketch.** Step 1: expand both conditional mutual informations as sums over the
values `z` of `Z` of the fiber mass times the mutual information under the fiber-conditioned
measure, distribute the factor `μ(A)`, and compare the sums term by term.
Step 2 (`z ∈ B`): the fiber `F = {Z = z}` lies inside `A`, so conditioning `μ[|A]` further on
`F` is the same as conditioning `μ` on `F`, and `μ(A) · μ[|A](F) = μ(F)`; the two terms are
equal.
Step 3 (`z ∉ B`): the fiber is disjoint from `A`, so its `μ[|A]`-mass is `0` and the left term
vanishes, while the right term is nonnegative because mutual information is. -/
theorem measureReal_mul_cond_condMutualInfo_le_condMutualInfo_of_event_eq_preimage
    {Ω₀ S₀ T₀ U₀ : Type*}
    [MeasurableSpace Ω₀] [MeasurableSpace S₀] [MeasurableSpace T₀] [MeasurableSpace U₀]
    [MeasurableSingletonClass S₀] [MeasurableSingletonClass T₀]
    [MeasurableSingletonClass U₀] [Countable S₀] [Countable T₀] [Countable U₀]
    (μ : Measure Ω₀) [IsProbabilityMeasure μ]
    (X : Ω₀ → S₀) (Y : Ω₀ → T₀) (Z : Ω₀ → U₀)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    {A : Set Ω₀} {B : Set U₀} (hB : MeasurableSet B) (hA : A = Z ⁻¹' B) :
    μ.real A * I[X : Y | Z ; μ[|A]] ≤ I[X : Y | Z ; μ] := by
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact hZ hB
  -- Step 1: expand both sides as fiber sums and compare termwise
  rw [condMutualInfo_eq_sum (μ := μ[|A]) hZ]
  rw [condMutualInfo_eq_sum (μ := μ) hZ]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hzrange
  let F : Set Ω₀ := Z ⁻¹' ({z} : Set U₀)
  have hFmeas : MeasurableSet F := hZ MeasurableSet.of_discrete
  by_cases hzB : z ∈ B
  -- Step 2: a fiber inside `A` contributes the same term on both sides
  · have hFA : F ⊆ A := by
      intro ω hω
      rw [hA]
      have hz : Z ω = z := by simpa [F] using hω
      simpa [hz] using hzB
    have hcond :
        μ[|A][|F] = μ[|F] :=
      cond_cond_eq_cond_of_subset μ hAmeas hFmeas hFA
    have hmass :
        μ.real A * (μ[|A]).real F = μ.real F :=
      measureReal_mul_cond_real_eq_measureReal_of_subset μ hAmeas hFA
    exact le_of_eq (by
      simpa [F] using
        (calc
          μ.real A * ((μ[|A]).real F * I[X : Y ; μ[|A][|F]])
              = (μ.real A * (μ[|A]).real F) * I[X : Y ; μ[|A][|F]] := by ring
          _ = μ.real F * I[X : Y ; μ[|F]] := by rw [hmass, hcond]))
  -- Step 3: a fiber outside `A` contributes `0` on the left and a nonnegative term on the right
  · have hAF_empty : A ∩ F = ∅ := by
      ext ω
      constructor
      · intro hω
        rw [hA] at hω
        have hz : Z ω = z := by simpa [F] using hω.2
        exact False.elim (hzB (by simpa [hz] using hω.1))
      · intro hω
        simp at hω
    have hcondReal : (μ[|A]).real F = 0 := by
      rw [ProbabilityTheory.cond_real_apply hAmeas, hAF_empty]
      simp
    have hright_nonneg :
        0 ≤ μ.real F * I[X : Y ; μ[|F]] :=
      mul_nonneg measureReal_nonneg (mutualInfo_nonneg hX hY _)
    calc
      μ.real A * ((μ[|A]).real F * I[X : Y ; μ[|A][|F]]) = 0 := by
        rw [hcondReal]
        ring
      _ ≤ μ.real F * I[X : Y ; μ[|F]] := hright_nonneg

/-- Chain rule for mutual information, splitting a pair on the right:
`I(X : (Y, W)) = I(X : Y) + I(X : W | Y)`. [RY20, Ch. 6, §Chain Rules] (chain rule for mutual
information, `I(AB:C) = I(A:C) + I(B:C|A)`, with the pair on the other side).

**Proof sketch.** Swapping the two components of the conditioning pair is injective, so
`H(X | W, Y) = H(X | Y, W)`; then expand both mutual informations as `H(X) − H(X | ·)` and the
conditional one as `H(X | Y) − H(X | W, Y)`, and close by `ring`. -/
theorem mutualInfo_prod_right_eq_add
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange W] :
    I[X : (fun ω => (Y ω, W ω)) ; μ] =
      I[X : Y ; μ] + I[X : W | Y ; μ] := by
  have hswap :
      H[X | (fun ω => (W ω, Y ω)) ; μ] =
        H[X | (fun ω => (Y ω, W ω)) ; μ] := by
    let swap : V × T → T × V := fun p => (p.2, p.1)
    have hswap_meas : Measurable (swap ∘ fun ω => (W ω, Y ω)) := by
      exact Measurable.of_discrete.comp (hW.prodMk hY)
    have h :=
      condEntropy_of_injective' μ hX (hW.prodMk hY) swap
        (fun a b h => by
          rcases a with ⟨aW, aY⟩
          rcases b with ⟨bW, bY⟩
          simp only [swap, Prod.mk.injEq] at h ⊢
          exact ⟨h.2, h.1⟩)
        hswap_meas
    simpa [swap, Function.comp_def] using h.symm
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hY.prodMk hW) μ,
    mutualInfo_eq_entropy_sub_condEntropy hX hY μ,
    condMutualInfo_eq' hX hW hY μ, hswap]
  ring

open Classical in
/-- Chain-rule rearrangement: if conditioning on `Y` does not increase the dependence between
`X` and `W` (`I(X : W | Y) ≤ I(X : W)`), then conditioning on `W` cannot increase the
information that `Y` has about `X` (`I(X : Y | W) ≤ I(X : Y)`).
[RY20, Ch. 6, §Subadditivity] (data processing / conditioning monotonicity, derived from the
chain rule).

**Proof sketch.** Step 1: swapping the components of a pair is injective, so
`I(X : (W, Y)) = I(X : (Y, W))`. Step 2: expand `I(X : (Y, W)) = I(X : Y) + I(X : W | Y)` and
`I(X : (W, Y)) = I(X : W) + I(X : Y | W)` by the chain rule `mutualInfo_prod_right_eq_add`.
Step 3: the two expansions agree by Step 1, so the hypothesis gives the claim by linear
arithmetic. -/
theorem condMutualInfo_le_mutualInfo_of_condDependence_le
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange W]
    (hdep : I[X : W|Y;μ] ≤ I[X : W ; μ]) :
    I[X : Y|W;μ] ≤ I[X : Y ; μ] := by
  -- Step 1: the two pair orderings carry the same information about `X`
  let swap : T × V → V × T := fun p => (p.2, p.1)
  have hswap_inj : Function.Injective swap := by
    intro a b h
    rcases a with ⟨aY, aW⟩
    rcases b with ⟨bY, bW⟩
    simp only [swap, Prod.mk.injEq] at h ⊢
    exact ⟨h.2, h.1⟩
  have hswap :
      I[X : (fun ω => (W ω, Y ω)) ; μ] =
        I[X : (fun ω => (Y ω, W ω)) ; μ] := by
    simpa [swap, Function.comp_def] using
      ProbabilityTheory.mutualInfo_comp_right_of_injective
        (μ := μ) (X := X) (Y := fun ω => (Y ω, W ω))
        hX (hY.prodMk hW) swap Measurable.of_discrete hswap_inj
  -- Step 2: chain rule in both orders
  have hYW :
      I[X : (fun ω => (Y ω, W ω)) ; μ] =
        I[X : Y ; μ] + I[X : W | Y ; μ] :=
    mutualInfo_prod_right_eq_add hX hY hW
  have hWY :
      I[X : (fun ω => (W ω, Y ω)) ; μ] =
        I[X : W ; μ] + I[X : Y | W ; μ] :=
    mutualInfo_prod_right_eq_add hX hW hY
  -- Step 3: combine with the hypothesis
  linarith

end ProbabilityTheory
