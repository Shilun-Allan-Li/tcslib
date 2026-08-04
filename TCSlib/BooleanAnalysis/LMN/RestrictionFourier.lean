import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.LMN.DecisionTreeFourier
import TCSlib.BooleanAnalysis.LMN.RestrictionCompose

set_option linter.unnecessarySeqFocus false

/-!
# Random Restrictions and the Fourier Spectrum (O'Donnell Proposition 4.17)

For a `δ`-random restriction `ρ` (each coordinate free with probability `δ`,
otherwise fixed to a uniform bit — the `bernoulliRestrWeight` measure) and
`f : {0,1}ⁿ → ℝ`:

* `expectation_fourierCoeff_restrictBF`:
    `E_ρ[f̂_ρ(S)] = δ^{|S|} · f̂(S)`
* `expectation_fourierCoeff_sq_restrictBF`:
    `E_ρ[f̂_ρ(S)²] = ∑_{U ⊇ S} δ^{|S|} (1−δ)^{|U\S|} · f̂(U)²`
* `bernoulliRestrProb_inter_freeVars`:
    `Pr_ρ[U ∩ J = S] = δ^{|S|} (1−δ)^{|U\S|}` for `S ⊆ U` (and `0` otherwise),
  where `J = ρ.freeVars` — so the second identity reads
    `E_ρ[f̂_ρ(S)²] = ∑_U Pr[U ∩ J = S] · f̂(U)²`, exactly O'Donnell's form.

The engine is the closed form for the Fourier coefficients of a restricted
function (`fourierCoeff_restrictBF`, playing the role of O'Donnell
Corollary 3.22):

  `f̂_ρ(S) = ∑_U 1[U ∩ J = S] · f̂(U) · (∏_{i ∈ U\J} sign of the bit ρ fixes)`

proved from the Walsh expansion and uniqueness of Fourier coefficients
(`DecisionTree.fourierCoeff_sum_chiS`). Instead of the textbook's two-stage
average (`E_z` for fixed `J`, then `E_J`), the expectation over `ρ` is computed
in one pass by factoring `bernoulliRestrWeight` per coordinate
(`bernoulliRestrWeight_eq_prod`): free coordinates contribute `δ`, fixed
coordinates average an odd sign to `0` (or a squared sign to `1−δ`), and
untouched coordinates contribute `1`.
-/

open BooleanAnalysis SwitchingLemma2 LMN
open Classical

noncomputable section

namespace RestrictionFourier

variable {n : ℕ}

/-! ## Restricting a real-valued Boolean function -/

/-- Restriction of a real-valued Boolean function: free coordinates read from
    the input, fixed coordinates from the restriction. Mirrors `restrictFn`. -/
def restrictBF (f : BooleanFunc n) (ρ : Restriction n) : BooleanFunc n :=
  fun x => f (ρ.extend x)

/-- Restriction commutes with the ±1-encoding of a Boolean-valued function. -/
lemma restrictBF_boolToSign (f : (Fin n → Bool) → Bool) (ρ : Restriction n) :
    restrictBF (fun x => boolToSign (f x)) ρ
      = fun x => boolToSign (restrictFn f ρ x) := rfl

/-- The product of the ±1-encodings of the bits `ρ` fixes on `T`
    (the value on free coordinates is a junk default, harmless under the
    indicators this is always paired with). -/
def signProd (ρ : Restriction n) (T : Finset (Fin n)) : ℝ :=
  ∏ i ∈ T, boolToSign ((ρ i).getD false)

lemma mem_freeVars {ρ : Restriction n} {i : Fin n} :
    i ∈ ρ.freeVars ↔ ρ i = none := by
  simp [Restriction.freeVars, Option.isNone_iff_eq_none]

/-- A character evaluated through a restriction splits into the free part
    (a character of the input) and the fixed part (a constant sign). -/
lemma chiS_extend (U : Finset (Fin n)) (ρ : Restriction n) (x : BoolCube n) :
    chiS U (ρ.extend x) = chiS (U ∩ ρ.freeVars) x * signProd ρ (U \ ρ.freeVars) := by
  unfold chiS signProd Restriction.extend
  rw [← Finset.prod_inter_mul_prod_diff U ρ.freeVars]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hfree : ρ i = none := mem_freeVars.mp (Finset.mem_inter.mp hi).2
    simp [hfree]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hfix : ¬ ρ i = none := fun h =>
      (Finset.mem_sdiff.mp hi).2 (mem_freeVars.mpr h)
    cases hv : ρ i with
    | none => exact absurd hv hfix
    | some b => rfl

/-! ## The Fourier coefficients of a restricted function (O'Donnell Cor. 3.22) -/

/-- **Closed form for restricted Fourier coefficients**:
    `f̂_ρ(S) = ∑_U 1[U ∩ J = S] · f̂(U) · signProd ρ (U \ J)` where
    `J = ρ.freeVars`. -/
theorem fourierCoeff_restrictBF (f : BooleanFunc n) (ρ : Restriction n)
    (S : Finset (Fin n)) :
    fourierCoeff (restrictBF f ρ) S
      = ∑ U : Finset (Fin n),
          (if U ∩ ρ.freeVars = S
            then fourierCoeff f U * signProd ρ (U \ ρ.freeVars) else 0) := by
  have hrepr : restrictBF f ρ = fun x => ∑ T : Finset (Fin n),
      (∑ U : Finset (Fin n), if U ∩ ρ.freeVars = T
        then fourierCoeff f U * signProd ρ (U \ ρ.freeVars) else 0) * chiS T x := by
    funext x
    calc restrictBF f ρ x
        = ∑ U : Finset (Fin n), fourierCoeff f U * chiS U (ρ.extend x) :=
          walsh_expansion f (ρ.extend x)
      _ = ∑ U : Finset (Fin n),
            fourierCoeff f U * signProd ρ (U \ ρ.freeVars)
              * chiS (U ∩ ρ.freeVars) x := by
          refine Finset.sum_congr rfl fun U _ => ?_
          rw [chiS_extend]; ring
      _ = ∑ U : Finset (Fin n), ∑ T : Finset (Fin n),
            (if U ∩ ρ.freeVars = T
              then fourierCoeff f U * signProd ρ (U \ ρ.freeVars) else 0)
              * chiS T x := by
          refine Finset.sum_congr rfl fun U _ => ?_
          simp [ite_mul, Finset.sum_ite_eq]
      _ = ∑ T : Finset (Fin n), (∑ U : Finset (Fin n),
            if U ∩ ρ.freeVars = T
              then fourierCoeff f U * signProd ρ (U \ ρ.freeVars) else 0)
              * chiS T x := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun T _ => (Finset.sum_mul _ _ _).symm
  rw [hrepr, DecisionTree.fourierCoeff_sum_chiS]

/-! ## Per-coordinate factorization of the Bernoulli measure -/

/-- Sums over all restrictions of per-coordinate products factor. -/
lemma sum_restriction_prod (h : Fin n → Option Bool → ℝ) :
    ∑ ρ : Restriction n, ∏ i : Fin n, h i (ρ i)
      = ∏ i : Fin n, ∑ v : Option Bool, h i v := by
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]

/-- Bernoulli-weighted sums of per-coordinate products factor, with the
    weight absorbed into each factor via `varWeight`. -/
lemma sum_bernoulli_prod (p : ℝ) (h : Fin n → Option Bool → ℝ) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ * ∏ i : Fin n, h i (ρ i)
      = ∏ i : Fin n, ∑ v : Option Bool, varWeight p v * h i v := by
  have hsplit : ∀ ρ : Restriction n,
      bernoulliRestrWeight p ρ * ∏ i : Fin n, h i (ρ i)
        = ∏ i : Fin n, varWeight p (ρ i) * h i (ρ i) := by
    intro ρ
    rw [bernoulliRestrWeight_eq_prod, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun ρ _ => hsplit ρ]
  exact sum_restriction_prod (fun i v => varWeight p v * h i v)

/-- Per-coordinate factor encoding the event `U ∩ freeVars = S` together with
    the sign the restriction assigns on `U \ S`:
    coordinates in `S` must be free, coordinates in `U \ S` must be fixed and
    contribute their sign, all others are unconstrained. -/
def localFactor (U S : Finset (Fin n)) (i : Fin n) (v : Option Bool) : ℝ :=
  if i ∈ S then (if v = none then 1 else 0)
  else if i ∈ U then (match v with | none => 0 | some b => boolToSign b)
  else 1

/-- The indicator-times-sign summand factors as a product of per-coordinate
    local factors (for `S ⊆ U`; otherwise the indicator is identically 0). -/
lemma indicator_signProd_eq_prod (U S : Finset (Fin n)) (hSU : S ⊆ U)
    (ρ : Restriction n) :
    (if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0)
      = ∏ i : Fin n, localFactor U S i (ρ i) := by
  by_cases hcond : U ∩ ρ.freeVars = S
  · rw [if_pos hcond]
    have hpt : ∀ i : Fin n, localFactor U S i (ρ i)
        = if i ∈ U \ S then boolToSign ((ρ i).getD false) else 1 := by
      intro i
      by_cases hiS : i ∈ S
      · have hfree : ρ i = none := by
          have h1 : i ∈ U ∩ ρ.freeVars := hcond.symm ▸ hiS
          exact mem_freeVars.mp (Finset.mem_inter.mp h1).2
        have hnot : i ∉ U \ S := fun h => (Finset.mem_sdiff.mp h).2 hiS
        simp [localFactor, hiS, hfree, hnot]
      · by_cases hiU : i ∈ U
        · have hfix : ρ i ≠ none := by
            intro hnone
            have hmem : i ∈ U ∩ ρ.freeVars :=
              Finset.mem_inter.mpr ⟨hiU, mem_freeVars.mpr hnone⟩
            rw [hcond] at hmem
            exact hiS hmem
          have hmem : i ∈ U \ S := Finset.mem_sdiff.mpr ⟨hiU, hiS⟩
          cases hv : ρ i with
          | none => exact absurd hv hfix
          | some b => simp [localFactor, hiS, hiU, hmem]
        · have hnot : i ∉ U \ S := fun h => hiU (Finset.mem_sdiff.mp h).1
          simp [localFactor, hiS, hiU, hnot]
    rw [Finset.prod_congr rfl fun i _ => hpt i]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
    have hset : U \ ρ.freeVars = U \ S := by
      ext j
      simp only [Finset.mem_sdiff, ← hcond, Finset.mem_inter]
      tauto
    rw [signProd, hset]
  · rw [if_neg hcond]
    have hex : ∃ i : Fin n, localFactor U S i (ρ i) = 0 := by
      by_contra hall
      push_neg at hall
      apply hcond
      ext i
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hiU, hiJ⟩
        by_contra hiS
        have hfree : ρ i = none := mem_freeVars.mp hiJ
        have := hall i
        simp [localFactor, hiS, hiU, hfree] at this
      · intro hiS
        refine ⟨hSU hiS, ?_⟩
        by_contra hiJ
        have hfix : ρ i ≠ none := fun h => hiJ (mem_freeVars.mpr h)
        have := hall i
        cases hv : ρ i with
        | none => exact hfix hv
        | some b => simp [localFactor, hiS, hv] at this
    obtain ⟨i₀, hi₀⟩ := hex
    exact (Finset.prod_eq_zero (Finset.mem_univ i₀) hi₀).symm

/-! ## Per-coordinate averages -/

/-- Averaging one local factor: free coords give `p`, sign coords average
    to `0`, unconstrained coords give `1`. -/
lemma sum_varWeight_localFactor (p : ℝ) (U S : Finset (Fin n)) (i : Fin n) :
    ∑ v : Option Bool, varWeight p v * localFactor U S i v
      = if i ∈ S then p else if i ∈ U then 0 else 1 := by
  by_cases hiS : i ∈ S <;> by_cases hiU : i ∈ U <;>
    simp [localFactor, varWeight, boolToSign, hiS, hiU] <;> ring

/-- Averaging a product of two local factors (for the squared coefficient):
    shared sign coordinates give `1 − p`, unmatched sign coordinates kill the
    term. -/
lemma sum_varWeight_localFactor_mul (p : ℝ) (U V S : Finset (Fin n)) (i : Fin n) :
    ∑ v : Option Bool, varWeight p v * (localFactor U S i v * localFactor V S i v)
      = if i ∈ S then p
        else if i ∈ U ∧ i ∈ V then (1 - p)
        else if i ∈ U ∨ i ∈ V then 0 else 1 := by
  by_cases hiS : i ∈ S <;> by_cases hiU : i ∈ U <;> by_cases hiV : i ∈ V <;>
    simp [localFactor, varWeight, boolToSign, hiS, hiU, hiV] <;> ring

/-- `∏_i (p on S, (1−p) on U∖S, 1 elsewhere) = p^{|S|} (1−p)^{|U∖S|}`. -/
lemma prod_if_subset (p : ℝ) (S U : Finset (Fin n)) :
    ∏ i : Fin n, (if i ∈ S then p else if i ∈ U then (1 - p) else 1)
      = p ^ S.card * (1 - p) ^ (U \ S).card := by
  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
  have h1 : ∏ i ∈ S, (if i ∈ S then p else if i ∈ U then (1 - p) else 1)
      = p ^ S.card := by
    rw [Finset.prod_congr rfl fun i hi => if_pos hi, Finset.prod_const]
  have h2 : ∏ i ∈ Finset.univ \ S,
      (if i ∈ S then p else if i ∈ U then (1 - p) else 1)
      = (1 - p) ^ (U \ S).card := by
    have hcong : ∀ i ∈ Finset.univ \ S,
        (if i ∈ S then p else if i ∈ U then (1 - p) else 1)
          = if i ∈ U then (1 - p) else 1 := by
      intro i hi
      rw [if_neg (Finset.mem_sdiff.mp hi).2]
    have hset : (Finset.univ \ S) ∩ U = U \ S := by
      ext j
      simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    rw [Finset.prod_congr rfl hcong, Finset.prod_ite_mem, hset, Finset.prod_const]
  rw [h1, h2, mul_comm]

/-! ## Proposition 4.17, first identity -/

/-- **O'Donnell Proposition 4.17 (first identity)**:
    `E_ρ[f̂_ρ(S)] = p^{|S|} · f̂(S)` under a Bernoulli(`p`)-random restriction. -/
theorem expectation_fourierCoeff_restrictBF (p : ℝ) (f : BooleanFunc n)
    (S : Finset (Fin n)) :
    ∑ ρ : Restriction n,
        bernoulliRestrWeight p ρ * fourierCoeff (restrictBF f ρ) S
      = p ^ S.card * fourierCoeff f S := by
  have hinner : ∀ U : Finset (Fin n),
      (∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
        (if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0))
      = if U = S then p ^ S.card else 0 := by
    intro U
    by_cases hSU : S ⊆ U
    · rw [Finset.sum_congr rfl fun ρ _ => by
        rw [indicator_signProd_eq_prod U S hSU ρ]]
      rw [sum_bernoulli_prod]
      rw [Finset.prod_congr rfl fun i _ => sum_varWeight_localFactor p U S i]
      by_cases hUS : U = S
      · subst hUS
        rw [if_pos rfl]
        have hcong : ∀ i : Fin n,
            (if i ∈ U then p else if i ∈ U then 0 else 1)
              = if i ∈ U then p else 1 := by
          intro i
          by_cases hi : i ∈ U <;> simp [hi]
        rw [Finset.prod_congr rfl fun i _ => hcong i]
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
      · obtain ⟨i₀, hi₀U, hi₀S⟩ :=
          Finset.exists_of_ssubset (hSU.ssubset_of_ne (Ne.symm hUS))
        rw [if_neg hUS]
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀S, hi₀U])
    · have hzero : ∀ ρ : Restriction n,
          (if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0) = 0 := by
        intro ρ
        rw [if_neg]
        intro h
        exact hSU (h ▸ Finset.inter_subset_left)
      rw [Finset.sum_congr rfl fun ρ _ => by rw [hzero ρ, mul_zero]]
      rw [Finset.sum_const_zero]
      rw [if_neg (by rintro rfl; exact hSU (Finset.Subset.refl _))]
  calc ∑ ρ : Restriction n,
        bernoulliRestrWeight p ρ * fourierCoeff (restrictBF f ρ) S
      = ∑ ρ : Restriction n, ∑ U : Finset (Fin n), fourierCoeff f U *
          (bernoulliRestrWeight p ρ *
            (if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0)) := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [fourierCoeff_restrictBF, Finset.mul_sum]
        refine Finset.sum_congr rfl fun U _ => ?_
        split_ifs <;> ring
    _ = ∑ U : Finset (Fin n), fourierCoeff f U *
          ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
            (if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun U _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ U : Finset (Fin n), fourierCoeff f U *
          (if U = S then p ^ S.card else 0) := by
        exact Finset.sum_congr rfl fun U _ => by rw [hinner U]
    _ = p ^ S.card * fourierCoeff f S := by
        simp [mul_ite, Finset.sum_ite_eq', mul_comm]

/-! ## Proposition 4.17, second identity -/

/-- **O'Donnell Proposition 4.17 (second identity)**:
    `E_ρ[f̂_ρ(S)²] = ∑_{U ⊇ S} p^{|S|} (1−p)^{|U∖S|} · f̂(U)²`. -/
theorem expectation_fourierCoeff_sq_restrictBF (p : ℝ) (f : BooleanFunc n)
    (S : Finset (Fin n)) :
    ∑ ρ : Restriction n,
        bernoulliRestrWeight p ρ * fourierCoeff (restrictBF f ρ) S ^ 2
      = ∑ U : Finset (Fin n),
          (if S ⊆ U
            then p ^ S.card * (1 - p) ^ (U \ S).card * fourierCoeff f U ^ 2
            else 0) := by
  have hinner : ∀ U V : Finset (Fin n),
      (∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
        ((if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0)
          * (if V ∩ ρ.freeVars = S then signProd ρ (V \ ρ.freeVars) else 0)))
      = if U = V ∧ S ⊆ U
          then p ^ S.card * (1 - p) ^ (U \ S).card else 0 := by
    intro U V
    by_cases hSU : S ⊆ U
    · by_cases hSV : S ⊆ V
      · rw [Finset.sum_congr rfl fun ρ _ => by
          rw [indicator_signProd_eq_prod U S hSU ρ,
            indicator_signProd_eq_prod V S hSV ρ, ← Finset.prod_mul_distrib]]
        rw [sum_bernoulli_prod p (fun i v => localFactor U S i v * localFactor V S i v)]
        rw [Finset.prod_congr rfl fun i _ =>
          sum_varWeight_localFactor_mul p U V S i]
        by_cases hUV : U = V
        · subst hUV
          rw [if_pos ⟨rfl, hSU⟩]
          have hcong : ∀ i : Fin n,
              (if i ∈ S then p
                else if i ∈ U ∧ i ∈ U then (1 - p)
                else if i ∈ U ∨ i ∈ U then 0 else 1)
              = if i ∈ S then p else if i ∈ U then (1 - p) else 1 := by
            intro i
            by_cases hiS : i ∈ S <;> by_cases hiU : i ∈ U <;>
              simp [hiS, hiU]
          rw [Finset.prod_congr rfl fun i _ => hcong i]
          exact prod_if_subset p S U
        · rw [if_neg (fun h => hUV h.1)]
          have hex : ∃ i : Fin n, (i ∈ U ∧ i ∉ V) ∨ (i ∈ V ∧ i ∉ U) := by
            by_contra hall
            push_neg at hall
            apply hUV
            ext i
            have := hall i
            tauto
          obtain ⟨i₀, hi₀⟩ := hex
          refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
          rcases hi₀ with ⟨hU, hV⟩ | ⟨hV, hU⟩
          · have hiS : i₀ ∉ S := fun h => hV (hSV h)
            simp [hiS, hU, hV]
          · have hiS : i₀ ∉ S := fun h => hU (hSU h)
            simp [hiS, hU, hV]
      · have hzero : ∀ ρ : Restriction n,
            (if V ∩ ρ.freeVars = S then signProd ρ (V \ ρ.freeVars) else 0)
              = 0 := by
          intro ρ
          rw [if_neg]
          intro h
          exact hSV (h ▸ Finset.inter_subset_left)
        rw [Finset.sum_congr rfl fun ρ _ => by rw [hzero ρ, mul_zero, mul_zero]]
        rw [Finset.sum_const_zero]
        rw [if_neg (by rintro ⟨rfl, hs⟩; exact hSV hs)]
    · have hzero : ∀ ρ : Restriction n,
          (if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0)
            = 0 := by
        intro ρ
        rw [if_neg]
        intro h
        exact hSU (h ▸ Finset.inter_subset_left)
      rw [Finset.sum_congr rfl fun ρ _ => by rw [hzero ρ, zero_mul, mul_zero]]
      rw [Finset.sum_const_zero]
      rw [if_neg (fun h => hSU h.2)]
  calc ∑ ρ : Restriction n,
        bernoulliRestrWeight p ρ * fourierCoeff (restrictBF f ρ) S ^ 2
      = ∑ ρ : Restriction n, ∑ U : Finset (Fin n), ∑ V : Finset (Fin n),
          fourierCoeff f U * fourierCoeff f V *
            (bernoulliRestrWeight p ρ *
              ((if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0)
                * (if V ∩ ρ.freeVars = S
                    then signProd ρ (V \ ρ.freeVars) else 0))) := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [pow_two, fourierCoeff_restrictBF, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun V _ => ?_
        split_ifs <;> ring
    _ = ∑ U : Finset (Fin n), ∑ V : Finset (Fin n),
          fourierCoeff f U * fourierCoeff f V *
            ∑ ρ : Restriction n, bernoulliRestrWeight p ρ *
              ((if U ∩ ρ.freeVars = S then signProd ρ (U \ ρ.freeVars) else 0)
                * (if V ∩ ρ.freeVars = S
                    then signProd ρ (V \ ρ.freeVars) else 0)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun V _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ U : Finset (Fin n), ∑ V : Finset (Fin n),
          fourierCoeff f U * fourierCoeff f V *
            (if U = V ∧ S ⊆ U
              then p ^ S.card * (1 - p) ^ (U \ S).card else 0) := by
        exact Finset.sum_congr rfl fun U _ =>
          Finset.sum_congr rfl fun V _ => by rw [hinner U V]
    _ = ∑ U : Finset (Fin n),
          (if S ⊆ U
            then p ^ S.card * (1 - p) ^ (U \ S).card * fourierCoeff f U ^ 2
            else 0) := by
        refine Finset.sum_congr rfl fun U _ => ?_
        by_cases hSU : S ⊆ U
        · rw [if_pos hSU]
          rw [Finset.sum_eq_single U]
          · rw [if_pos ⟨rfl, hSU⟩]
            ring
          · intro V _ hVU
            rw [if_neg (fun h => hVU h.1.symm), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ U) h
        · rw [if_neg hSU]
          rw [Finset.sum_congr rfl fun V _ => by
            rw [if_neg (fun h => hSU h.2), mul_zero]]
          exact Finset.sum_const_zero

/-! ## The probability form: `Pr[U ∩ J = S]` -/

/-- The squared sign product is 1. -/
lemma signProd_sq (ρ : Restriction n) (T : Finset (Fin n)) :
    signProd ρ T ^ 2 = 1 := by
  rw [signProd, ← Finset.prod_pow]
  rw [Finset.prod_congr rfl fun i _ => boolToSign_sq ((ρ i).getD false)]
  exact Finset.prod_const_one

/-- **Proposition 4.17, probability form**: for a Bernoulli(`p`)-random
    restriction, `Pr[U ∩ J = S] = p^{|S|} (1−p)^{|U∖S|}` when `S ⊆ U`
    (and `0` otherwise). Obtained by applying the squared-coefficient identity
    to `f = χ_U`. Together with `expectation_fourierCoeff_sq_restrictBF` this
    gives O'Donnell's `E[f̂_ρ(S)²] = ∑_U Pr[U ∩ J = S]·f̂(U)²`. -/
theorem bernoulliRestrProb_inter_freeVars (p : ℝ) (U S : Finset (Fin n)) :
    bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S)
      = if S ⊆ U then p ^ S.card * (1 - p) ^ (U \ S).card else 0 := by
  have hLHS : ∀ ρ : Restriction n,
      fourierCoeff (restrictBF (chiS U) ρ) S ^ 2
        = if U ∩ ρ.freeVars = S then 1 else 0 := by
    intro ρ
    rw [fourierCoeff_restrictBF]
    have hterm : ∀ U' : Finset (Fin n),
        (if U' ∩ ρ.freeVars = S
          then fourierCoeff (chiS U) U' * signProd ρ (U' \ ρ.freeVars) else 0)
        = if U = U'
            then (if U' ∩ ρ.freeVars = S
              then signProd ρ (U' \ ρ.freeVars) else 0)
            else 0 := by
      intro U'
      have hc : fourierCoeff (chiS U) U' = if U = U' then 1 else 0 :=
        fourier_coeff_chi U U'
      rw [hc]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun U' _ => hterm U', Finset.sum_ite_eq,
      if_pos (Finset.mem_univ U)]
    split_ifs with h
    · rw [signProd_sq]
    · rw [zero_pow (by norm_num)]
  have key := expectation_fourierCoeff_sq_restrictBF p (chiS U) S
  rw [Finset.sum_congr rfl fun ρ _ => by rw [hLHS ρ]] at key
  unfold bernoulliRestrProb
  rw [key]
  have hRHS : ∀ U' : Finset (Fin n),
      (if S ⊆ U'
        then p ^ S.card * (1 - p) ^ (U' \ S).card * fourierCoeff (chiS U) U' ^ 2
        else 0)
      = if U = U'
          then (if S ⊆ U' then p ^ S.card * (1 - p) ^ (U' \ S).card else 0)
          else 0 := by
    intro U'
    have hc : fourierCoeff (chiS U) U' = if U = U' then 1 else 0 :=
      fourier_coeff_chi U U'
    rw [hc]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun U' _ => hRHS U', Finset.sum_ite_eq,
    if_pos (Finset.mem_univ U)]

end RestrictionFourier
