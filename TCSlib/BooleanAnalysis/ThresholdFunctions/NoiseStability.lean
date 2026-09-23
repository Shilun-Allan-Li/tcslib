import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TCSlib.BooleanAnalysis.ThresholdFunctions.DegreeOne
import TCSlib.BooleanAnalysis.ThresholdFunctions.Fourier
import TCSlib.BooleanAnalysis.ThresholdFunctions.BitFlipSets
import TCSlib.BooleanAnalysis.ThresholdFunctions.LinearThresholdInfluence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform noise stability of threshold functions

This file states Peres's theorem, the general influence-to-noise reduction used in its proof, and
the Chapter 5 bound for polynomial threshold functions.

## Main definitions

* `BooleanFunctionClass`, `IsBooleanValuedClass`, and `IsUniformlyNoiseStable`.
* `identifiedNegation` and the closure property used by the reduction theorem.
* `polynomialThresholdClass`.

## Main results

* `influence_bound_implies_noise_bound`: Theorem 5.35.
* `peres_theorem`: all LTFs have noise sensitivity `O(sqrt δ)`.
* `kane_totalInfluence_bound`: the Chapter 5 bound for degree-`k` PTFs and its noise consequence.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, §5.5.
* [Per04] Y. Peres, Noise stability of weighted majority, 2004.
* [Kan12] D. Kane, The Gaussian surface area and noise sensitivity of degree-`d` polynomial
  threshold functions, 2012.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

/-! ## Classes of Boolean functions -/

/-- A dimension-indexed class of real-valued functions on Boolean cubes. -/
abbrev BooleanFunctionClass := ∀ n : ℕ, Set (BooleanFunc n)

/-- A function class is Boolean-valued when every member takes values in `{−1, 1}`. -/
def IsBooleanValuedClass (B : BooleanFunctionClass) : Prop :=
  ∀ {n : ℕ} {f : BooleanFunc n}, f ∈ B n → isPmOne f

/-- The class of degree-at-most-`k` polynomial threshold functions.

[OD14, §5.5] -/
def polynomialThresholdClass (k n : ℕ) : Set (BooleanFunc n) :=
  {f | isPmOne f ∧ IsPolynomialThreshold f k}

/-- The class of all linear threshold functions. -/
def linearThresholdClass (n : ℕ) : Set (BooleanFunc n) :=
  {f | isPmOne f ∧ IsLinearThreshold f}

/-- A class is uniformly noise-stable when one `[0,1]`-valued modulus on noise rates in
`[0,1/2]`, tending to zero with the noise rate, uniformly bounds the noise sensitivity of every
member in every dimension. The modulus is represented as a total real function for convenience,
with its source-prescribed range enforced on `[0,1/2]`.

[OD14, Def. 5.34] -/
def IsUniformlyNoiseStable (B : BooleanFunctionClass) : Prop :=
  IsBooleanValuedClass B ∧
    ∃ ε : ℝ → ℝ,
      (∀ δ ∈ Set.Icc (0 : ℝ) (1 / 2), ε δ ∈ Set.Icc (0 : ℝ) 1) ∧
        Filter.Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        ∀ {n : ℕ} {f : BooleanFunc n}, f ∈ B n → ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
          noiseSensitivity δ f ≤ ε δ

/-- Negate selected inputs and identify the original variables according to `π`.

[OD14, Thm. 5.35] -/
noncomputable def identifiedNegation {n m : ℕ} (f : BooleanFunc n) (z : BoolCube n)
    (π : Fin n → Fin m) : BooleanFunc m :=
  fun w ↦ f fun i ↦ if z i then !(w (π i)) else w (π i)

/-- A function class is closed under identifying and negating input variables.

[OD14, Thm. 5.35] -/
def IsClosedUnderInputNegationAndIdentification (B : BooleanFunctionClass) : Prop :=
  ∀ {n m : ℕ} {f : BooleanFunc n}, f ∈ B n →
    ∀ (z : BoolCube n) (π : Fin n → Fin m), identifiedNegation f z π ∈ B m

/-- The number of blocks used by the random-partition proof of Theorem 5.35. -/
noncomputable def noiseBlockCount (δ : ℝ) : ℕ :=
  Nat.floor δ⁻¹

/-! ## Elementary bounds on noise sensitivity -/

/-- At nonnegative correlation the noise stability of any function is nonnegative. -/
lemma noiseStability_nonneg {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (f : BooleanFunc n) :
    0 ≤ noiseStability ρ f := by
  rw [noiseStability, stability_formula]
  exact Finset.sum_nonneg fun S _ ↦ by positivity

/-- At noise rates in `[0, 1/2]` the noise sensitivity never exceeds `1/2`. -/
lemma noiseSensitivity_le_half {n : ℕ} {δ : ℝ} (hδ : δ ≤ 1 / 2) (f : BooleanFunc n) :
    noiseSensitivity δ f ≤ 1 / 2 := by
  have h : 0 ≤ noiseStability (1 - 2 * δ) f := noiseStability_nonneg (by linarith) f
  unfold noiseSensitivity
  linarith

/-! ## Closure properties of the threshold classes -/

lemma linearThresholdClass_isBooleanValued : IsBooleanValuedClass linearThresholdClass :=
  fun hf ↦ hf.1

/-- Linear threshold functions are closed under negating and identifying input variables: the
identified function is the sign of the affine form whose `j`-th coefficient is the signed sum of
the original coefficients over the fibre of `j`. [OD14, Thm. 5.35] -/
lemma linearThresholdClass_closed :
    IsClosedUnderInputNegationAndIdentification linearThresholdClass := by
  classical
  intro n m f hf z π
  obtain ⟨-, hltf⟩ := hf
  obtain ⟨c, a, rfl⟩ := hltf.exists_affine
  have key : identifiedNegation
      (fun x : BoolCube n ↦ thresholdSign (c + ∑ i : Fin n, a i * boolToSign (x i))) z π
      = fun w : BoolCube m ↦ thresholdSign (c + ∑ j : Fin m,
          (∑ i ∈ Finset.univ.filter (fun i ↦ π i = j), a i * boolToSign (z i))
            * boolToSign (w j)) := by
    funext w
    have hsign : ∀ i : Fin n,
        a i * boolToSign (if z i then !(w (π i)) else w (π i))
          = a i * boolToSign (z i) * boolToSign (w (π i)) := by
      intro i
      cases hz : z i <;> simp
    have hfib : ∑ i : Fin n, a i * boolToSign (z i) * boolToSign (w (π i))
        = ∑ j : Fin m, (∑ i ∈ Finset.univ.filter (fun i ↦ π i = j),
            a i * boolToSign (z i)) * boolToSign (w j) := by
      rw [← Finset.sum_fiberwise Finset.univ π
        (fun i ↦ a i * boolToSign (z i) * boolToSign (w (π i)))]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [(Finset.mem_filter.mp hi).2]
    simp only [identifiedNegation]
    congr 1
    calc c + ∑ i : Fin n, a i * boolToSign (if z i then !(w (π i)) else w (π i))
        = c + ∑ i : Fin n, a i * boolToSign (z i) * boolToSign (w (π i)) := by
          rw [Finset.sum_congr rfl fun i _ ↦ hsign i]
      _ = _ := by rw [hfib]
  rw [key]
  exact ⟨isPmOne_thresholdSign _, isLinearThreshold_affine _ _⟩

/-! ### Closure of the polynomial threshold classes -/

/-- The set of blocks that the coordinates of `S` hit an odd number of times under the
identification `π`. -/
def oddFiberImage {n m : ℕ} (π : Fin n → Fin m) (S : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun j ↦ Odd (S.filter fun i ↦ π i = j).card

lemma oddFiberImage_card_le {n m : ℕ} (π : Fin n → Fin m) (S : Finset (Fin n)) :
    (oddFiberImage π S).card ≤ S.card := by
  classical
  have hsub : oddFiberImage π S ⊆ S.image π := by
    intro j hj
    simp only [oddFiberImage, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hne : (S.filter fun i ↦ π i = j).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (S.filter fun i ↦ π i = j) with h | h
      · rw [h] at hj; simp at hj
      · exact h
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_filter] at hi
    exact Finset.mem_image.mpr ⟨i, hi.1, hi.2⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

lemma boolToSign_pow (b : Bool) (c : ℕ) :
    boolToSign b ^ c = if Odd c then boolToSign b else 1 := by
  cases b with
  | false => simp [boolToSign]
  | true =>
    rcases Nat.even_or_odd c with hc | hc
    · rw [if_neg (by simpa [Nat.not_odd_iff_even] using hc)]
      simpa [boolToSign] using hc.neg_one_pow
    · rw [if_pos hc]
      simpa [boolToSign] using hc.neg_one_pow

/-- Identifying coordinates along `π` turns a Walsh character of `S` into the Walsh character of
the blocks that `S` meets oddly often. -/
lemma prod_boolToSign_comp {n m : ℕ} (π : Fin n → Fin m) (S : Finset (Fin n)) (w : BoolCube m) :
    ∏ i ∈ S, boolToSign (w (π i)) = ∏ j ∈ oddFiberImage π S, boolToSign (w j) := by
  classical
  rw [← Finset.prod_fiberwise S π fun i ↦ boolToSign (w (π i))]
  have h1 : ∀ j : Fin m, (∏ i ∈ S.filter fun i ↦ π i = j, boolToSign (w (π i)))
      = boolToSign (w j) ^ (S.filter fun i ↦ π i = j).card := by
    intro j
    rw [Finset.prod_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2]]
    exact Finset.prod_const _
  simp_rw [h1, boolToSign_pow]
  rw [oddFiberImage, Finset.prod_filter]

/-- The Walsh character of `S` at an identified and negated input factors as the character of the
negation pattern times the character of the odd-fibre image. -/
lemma chiS_identifiedNegation {n m : ℕ} (z : BoolCube n) (π : Fin n → Fin m) (w : BoolCube m)
    (S : Finset (Fin n)) :
    chiS S (fun i ↦ if z i then !(w (π i)) else w (π i))
      = chiS S z * chiS (oddFiberImage π S) w := by
  simp only [chiS]
  rw [← prod_boolToSign_comp π S w, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases h : z i <;> cases hw : w (π i) <;> simp [boolToSign]

/-- Degree-`k` polynomial threshold functions are closed under negating and identifying input
variables: substituting `x_i = z_i w_{π(i)}` into a degree-`k` multilinear polynomial produces a
degree-`k` multilinear polynomial in `w`. [OD14, Thm. 5.35] -/
lemma polynomialThresholdClass_closed (k : ℕ) :
    IsClosedUnderInputNegationAndIdentification (polynomialThresholdClass k) := by
  classical
  intro n m f hf z π
  obtain ⟨-, p, hdeg, hrep⟩ := hf
  set q : MultilinearPolynomial m := fun T ↦
    ∑ S ∈ Finset.univ.filter fun S : Finset (Fin n) ↦ oddFiberImage π S = T,
      p S * chiS S z with hq
  have hqdeg : q.HasDegreeAtMost k := by
    intro T hT
    refine Finset.sum_eq_zero fun S hS ↦ ?_
    have hST : T = oddFiberImage π S := ((Finset.mem_filter.mp hS).2).symm
    have hcard : k < S.card := lt_of_lt_of_le hT (hST ▸ oddFiberImage_card_le π S)
    rw [hdeg S hcard, zero_mul]
  have heval : ∀ w : BoolCube m,
      q.eval w = p.eval fun i ↦ if z i then !(w (π i)) else w (π i) := by
    intro w
    have key : ∀ T : Finset (Fin m),
        (∑ S ∈ Finset.univ.filter fun S : Finset (Fin n) ↦ oddFiberImage π S = T,
            p S * chiS S z) * chiS T w
          = ∑ S ∈ Finset.univ.filter fun S : Finset (Fin n) ↦ oddFiberImage π S = T,
              p S * chiS S z * chiS (oddFiberImage π S) w := by
      intro T
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun S hS ↦ ?_
      rw [(Finset.mem_filter.mp hS).2]
    calc q.eval w
        = ∑ T : Finset (Fin m),
            (∑ S ∈ Finset.univ.filter fun S : Finset (Fin n) ↦ oddFiberImage π S = T,
              p S * chiS S z) * chiS T w := rfl
      _ = ∑ T : Finset (Fin m),
            ∑ S ∈ Finset.univ.filter fun S : Finset (Fin n) ↦ oddFiberImage π S = T,
              p S * chiS S z * chiS (oddFiberImage π S) w :=
            Finset.sum_congr rfl fun T _ ↦ key T
      _ = ∑ S : Finset (Fin n), p S * chiS S z * chiS (oddFiberImage π S) w :=
            Finset.sum_fiberwise Finset.univ _ _
      _ = p.eval fun i ↦ if z i then !(w (π i)) else w (π i) := by
            simp only [MultilinearPolynomial.eval]
            exact Finset.sum_congr rfl fun S _ ↦ by
              rw [chiS_identifiedNegation z π w S, mul_assoc]
  have hfun : identifiedNegation f z π = q.threshold := by
    funext w
    show f (fun i ↦ if z i then !(w (π i)) else w (π i)) = thresholdSign (q.eval w)
    rw [heval w, ← hrep]
    rfl
  rw [hfun]
  exact ⟨isPmOne_thresholdSign _, q, hqdeg, rfl⟩

/-- Raising the allowed degree enlarges the class of polynomial threshold functions. -/
lemma polynomialThresholdClass_mono {k k' : ℕ} (h : k ≤ k') (n : ℕ) :
    polynomialThresholdClass k n ⊆ polynomialThresholdClass k' n := by
  rintro f ⟨hpm, p, hdeg, hrep⟩
  exact ⟨hpm, p, fun S hS ↦ hdeg S (lt_of_le_of_lt h hS), hrep⟩

/-! ## The random-partition identity -/

/-- Identifying variables along `π` and negating according to `z` rewrites the input as an
exclusive-or. -/
lemma identifiedNegation_apply {n m : ℕ} (f : BooleanFunc n) (z : BoolCube n)
    (π : Fin n → Fin m) (w : BoolCube m) :
    identifiedNegation f z π w = f (xorVec z (fun i ↦ w (π i))) := by
  unfold identifiedNegation xorVec
  congr 1
  funext i
  cases z i <;> simp

/-- Flipping the `j₀`-th variable of the identified function flips exactly the block `π⁻¹(j₀)` of
the original input. -/
lemma identifiedNegation_flip {n m : ℕ} (f : BooleanFunc n) (z : BoolCube n)
    (π : Fin n → Fin m) (w : BoolCube m) (j₀ : Fin m) :
    identifiedNegation f z π (flipBit w j₀)
      = f (flipSet (xorVec z (fun i ↦ w (π i))) (fiber π j₀)) := by
  rw [identifiedNegation_apply]
  congr 1
  funext i
  simp only [xorVec, flipSet]
  by_cases h : π i = j₀
  · rw [if_pos (mem_fiber.mpr h)]
    have h1 : flipBit w j₀ (π i) = !(w (π i)) := by rw [h]; simp [flipBit]
    rw [h1]
    cases z i <;> simp
  · rw [if_neg (fun hc ↦ h (mem_fiber.mp hc))]
    have h1 : flipBit w j₀ (π i) = w (π i) := by simp [flipBit, Function.update_of_ne h]
    rw [h1]

/-- Averaging over the negation pattern turns the influence of a block variable into the
disagreement probability of the corresponding block flip. -/
lemma expect_influence_identifiedNegation {n m : ℕ} (f : BooleanFunc n) (π : Fin n → Fin m)
    (j₀ : Fin m) :
    expect (fun z : BoolCube n ↦ influence j₀ (identifiedNegation f z π))
      = flipDisagreement f (fiber π j₀) := by
  have hQ : ∀ (z : BoolCube n) (w : BoolCube m),
      (identifiedNegation f z π w - identifiedNegation f z π (flipBit w j₀)) ^ 2 / 4
        = (f (xorVec z (fun i ↦ w (π i)))
            - f (flipSet (xorVec z (fun i ↦ w (π i))) (fiber π j₀))) ^ 2 / 4 := by
    intro z w
    rw [identifiedNegation_apply, identifiedNegation_flip]
  have hinner : ∀ w : BoolCube m,
      uniformWeight n * ∑ z : BoolCube n,
          (identifiedNegation f z π w - identifiedNegation f z π (flipBit w j₀)) ^ 2 / 4
        = flipDisagreement f (fiber π j₀) := by
    intro w
    have h : ∑ z : BoolCube n, (f (xorVec z (fun i ↦ w (π i)))
          - f (flipSet (xorVec z (fun i ↦ w (π i))) (fiber π j₀))) ^ 2 / 4
        = ∑ x : BoolCube n, (f x - f (flipSet x (fiber π j₀))) ^ 2 / 4 :=
      sum_comp_xorVec (fun x ↦ (f x - f (flipSet x (fiber π j₀))) ^ 2 / 4) (fun i ↦ w (π i))
    rw [Finset.sum_congr rfl (fun z _ ↦ hQ z w), h]
    simp only [flipDisagreement, expect]
  calc expect (fun z : BoolCube n ↦ influence j₀ (identifiedNegation f z π))
      = uniformWeight n * ∑ z : BoolCube n, (uniformWeight m * ∑ w : BoolCube m,
          (identifiedNegation f z π w - identifiedNegation f z π (flipBit w j₀)) ^ 2 / 4) := by
        simp only [expect, influence]
    _ = uniformWeight m * ∑ w : BoolCube m, (uniformWeight n * ∑ z : BoolCube n,
          (identifiedNegation f z π w - identifiedNegation f z π (flipBit w j₀)) ^ 2 / 4) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun z _ ↦ by ring
    _ = uniformWeight m * ∑ _w : BoolCube m, flipDisagreement f (fiber π j₀) := by
        rw [Finset.sum_congr rfl (fun w _ ↦ hinner w)]
    _ = flipDisagreement f (fiber π j₀) := by
      change expect (fun _ : BoolCube m ↦ flipDisagreement f (fiber π j₀)) = _
      rw [expect_eq_fintypeExpect]
      exact Fintype.expect_const _

/-- Averaging the block-flip disagreement over a uniformly random colouring of the coordinates
recovers the noise sensitivity at rate `1/m`. -/
lemma sum_flipDisagreement_fiber {n m : ℕ} {f : BooleanFunc n} (hf : isPmOne f) (hm : 0 < m)
    (j₀ : Fin m) :
    ∑ π : Fin n → Fin m, flipDisagreement f (fiber π j₀)
      = (m : ℝ) ^ n * noiseSensitivity (1 / m) f := by
  have hcard : (Finset.univ (α := Fin n → Fin m)).card = m ^ n := by
    simp [Finset.card_univ]
  have hswap : ∑ π : Fin n → Fin m,
        ∑ T : Finset (Fin n), (-1 : ℝ) ^ (T ∩ fiber π j₀).card * fourierCoeff f T ^ 2
      = (m : ℝ) ^ n * ∑ T : Finset (Fin n), (1 - 2 / (m : ℝ)) ^ T.card * fourierCoeff f T ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ ↦ ?_
    rw [← Finset.sum_mul, sum_pi_sign hm j₀ T]
    ring
  have hstab : noiseStability (1 - 2 * (1 / (m : ℝ))) f
      = ∑ T : Finset (Fin n), (1 - 2 / (m : ℝ)) ^ T.card * fourierCoeff f T ^ 2 := by
    rw [noiseStability, stability_formula,
      show (1 : ℝ) - 2 * (1 / (m : ℝ)) = 1 - 2 / (m : ℝ) from by ring]
  simp only [flipDisagreement_eq hf]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hswap]
  simp only [Finset.sum_const, hcard, nsmul_eq_mul, mul_one, noiseSensitivity, hstab]
  push_cast
  ring

/-! ## Influence-to-noise reduction and Peres's theorem -/

/-- Noise sensitivity is monotone in the noise rate on `[0, 1/2]`. -/
lemma noiseSensitivity_mono {n : ℕ} (f : BooleanFunc n) {δ δ' : ℝ}
    (hle : δ ≤ δ') (h1 : δ' ≤ 1 / 2) :
    noiseSensitivity δ f ≤ noiseSensitivity δ' f := by
  have hstab : noiseStability (1 - 2 * δ') f ≤ noiseStability (1 - 2 * δ) f := by
    rw [noiseStability, noiseStability, stability_formula, stability_formula]
    refine Finset.sum_le_sum fun T _ ↦ ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  unfold noiseSensitivity
  linarith

/-- If a class is closed under negating and identifying variables and every `m`-variable member has
total influence at most `A(m)`, then its noise sensitivity at rate `δ` is at most
`A(⌊1/δ⌋) / ⌊1/δ⌋`. [OD14, Thm. 5.35]

**Proof sketch.** Randomly partition the input coordinates into `m = ⌊1/δ⌋` blocks, negate a
uniformly random block, and view the induced function as an `m`-variable member of the class. Its
average influence is at most `A(m)/m`. Averaging over the partition gives exactly the original
noise-sensitivity experiment. -/
theorem influence_bound_implies_noise_bound (B : BooleanFunctionClass) (A : ℕ → ℝ)
    (hbool : IsBooleanValuedClass B)
    (hclosed : IsClosedUnderInputNegationAndIdentification B)
    (hInf : ∀ {n : ℕ} {f : BooleanFunc n}, f ∈ B n → totalInfluence f ≤ A n)
    {δ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    ∀ {n : ℕ} {f : BooleanFunc n}, f ∈ B n →
      noiseSensitivity δ f ≤ A (noiseBlockCount δ) / noiseBlockCount δ := by
  intro n f hf
  obtain ⟨hδ0, hδ2⟩ := hδ
  have hfb : isPmOne f := hbool hf
  set M : ℕ := noiseBlockCount δ with hM
  have hinv2 : (2 : ℝ) ≤ δ⁻¹ := by
    have h := inv_anti₀ hδ0 hδ2
    norm_num at h
    linarith
  have hM2 : 2 ≤ M := by
    rw [hM, noiseBlockCount]
    exact Nat.le_floor (by exact_mod_cast hinv2)
  have hMpos : 0 < M := by omega
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hM2R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hfloorle : (M : ℝ) ≤ δ⁻¹ := by
    rw [hM, noiseBlockCount]
    exact Nat.floor_le (by positivity)
  have hδM : δ ≤ 1 / (M : ℝ) := by
    rw [le_div_iff₀ hMposR]
    have h := mul_le_mul_of_nonneg_left hfloorle (le_of_lt hδ0)
    rw [mul_inv_cancel₀ (ne_of_gt hδ0)] at h
    linarith
  have hhalf : 1 / (M : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num) hM2R
  -- the random-partition identity, summed over blocks
  have hsum1 : ∀ j₀ : Fin M, ∑ π : Fin n → Fin M,
      expect (fun z ↦ influence j₀ (identifiedNegation f z π))
        = (M : ℝ) ^ n * noiseSensitivity (1 / (M : ℝ)) f := by
    intro j₀
    rw [Finset.sum_congr rfl (fun π _ ↦ expect_influence_identifiedNegation f π j₀)]
    exact sum_flipDisagreement_fiber hfb hMpos j₀
  have hleft : ∑ j₀ : Fin M, ∑ π : Fin n → Fin M,
      expect (fun z ↦ influence j₀ (identifiedNegation f z π))
        = (M : ℝ) * ((M : ℝ) ^ n * noiseSensitivity (1 / (M : ℝ)) f) := by
    rw [Finset.sum_congr rfl (fun j₀ _ ↦ hsum1 j₀)]
    simp [Finset.card_univ]
  have hright : ∑ j₀ : Fin M, ∑ π : Fin n → Fin M,
      expect (fun z ↦ influence j₀ (identifiedNegation f z π)) ≤ (M : ℝ) ^ n * A M := by
    rw [Finset.sum_comm]
    have hterm : ∀ π : Fin n → Fin M,
        ∑ j₀ : Fin M, expect (fun z ↦ influence j₀ (identifiedNegation f z π)) ≤ A M := by
      intro π
      calc
        ∑ j₀ : Fin M, expect (fun z ↦ influence j₀ (identifiedNegation f z π)) =
            ∑ j₀ : Fin M, 𝔼 z, influence j₀ (identifiedNegation f z π) := by
              simp_rw [expect_eq_fintypeExpect]
        _ = 𝔼 z : BoolCube n, ∑ j₀ : Fin M,
            influence j₀ (identifiedNegation f z π) :=
              (Finset.expect_sum_comm Finset.univ Finset.univ _).symm
        _ ≤ 𝔼 _z : BoolCube n, A M :=
          Finset.expect_le_expect fun z _ ↦ hInf (hclosed hf z π)
        _ = A M := Fintype.expect_const _
    calc ∑ π : Fin n → Fin M,
          ∑ j₀ : Fin M, expect (fun z ↦ influence j₀ (identifiedNegation f z π))
        ≤ ∑ _π : Fin n → Fin M, A M := Finset.sum_le_sum fun π _ ↦ hterm π
      _ = (M : ℝ) ^ n * A M := by simp [Finset.card_univ]
  have hMn : (0 : ℝ) < (M : ℝ) ^ n := by positivity
  have hcomb : (M : ℝ) ^ n * ((M : ℝ) * noiseSensitivity (1 / (M : ℝ)) f)
      ≤ (M : ℝ) ^ n * A M := by
    calc (M : ℝ) ^ n * ((M : ℝ) * noiseSensitivity (1 / (M : ℝ)) f)
        = (M : ℝ) * ((M : ℝ) ^ n * noiseSensitivity (1 / (M : ℝ)) f) := by ring
      _ = ∑ j₀ : Fin M, ∑ π : Fin n → Fin M,
            expect (fun z ↦ influence j₀ (identifiedNegation f z π)) := hleft.symm
      _ ≤ (M : ℝ) ^ n * A M := hright
  have hfinal : (M : ℝ) * noiseSensitivity (1 / (M : ℝ)) f ≤ A M :=
    le_of_mul_le_mul_left hcomb hMn
  have hmono : noiseSensitivity δ f ≤ noiseSensitivity (1 / (M : ℝ)) f :=
    noiseSensitivity_mono f hδM hhalf
  rw [le_div_iff₀ hMposR]
  nlinarith [hmono, hfinal, hMposR]

/-- Every linear threshold function has noise sensitivity at most a universal constant times
`sqrt δ`. [OD14, §5.5, Peres's Theorem; Per04]

**Proof sketch.** LTFs are closed under input negation and identification. Every `m`-variable LTF is
unate, hence has total influence at most `sqrt m`. Apply
`influence_bound_implies_noise_bound` with `A(m) = sqrt m` and `m = ⌊1/δ⌋`. -/
theorem peres_theorem :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} {f : BooleanFunc n}, f ∈ linearThresholdClass n →
      ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2), noiseSensitivity δ f ≤ C * Real.sqrt δ := by
  refine ⟨Real.sqrt 2, Real.sqrt_nonneg 2, ?_⟩
  intro n f hf δ hδ
  obtain ⟨hδ0, hδ2⟩ := hδ
  have hbase := influence_bound_implies_noise_bound linearThresholdClass
    (fun m ↦ Real.sqrt m) linearThresholdClass_isBooleanValued linearThresholdClass_closed
    (fun {_ _} hg ↦ ltf_totalInfluence_le_sqrt hg.2) ⟨hδ0, hδ2⟩ hf
  set M : ℕ := noiseBlockCount δ with hM
  have hinv2 : (2 : ℝ) ≤ δ⁻¹ := by
    have h := inv_anti₀ hδ0 hδ2
    norm_num at h
    linarith
  have hfloor : δ⁻¹ < (M : ℝ) + 1 := by
    rw [hM, noiseBlockCount]
    exact Nat.lt_floor_add_one _
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hMlb : δ⁻¹ / 2 ≤ (M : ℝ) := by linarith
  have hsqrtM : Real.sqrt M * Real.sqrt M = (M : ℝ) := Real.mul_self_sqrt (le_of_lt hMpos)
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have h2dM : (1 : ℝ) ≤ 2 * δ * M := by
    have hid : δ * δ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hδ0)
    nlinarith [hMlb, hδ0]
  have hkey : (1 : ℝ) ≤ Real.sqrt 2 * Real.sqrt δ * Real.sqrt M := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_mul (by positivity)]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (2 * δ * M) := Real.sqrt_le_sqrt h2dM
  calc noiseSensitivity δ f ≤ Real.sqrt M / M := hbase
    _ = 1 / Real.sqrt M := by
        rw [div_eq_div_iff (ne_of_gt hMpos) (ne_of_gt hsM), one_mul, hsqrtM]
    _ ≤ Real.sqrt 2 * Real.sqrt δ := by
        rw [div_le_iff₀ hsM]
        nlinarith [hkey]

/-- The class of all linear threshold functions is uniformly noise-stable.
[OD14, §5.5, consequence of Peres's Theorem]

**Proof sketch.** Use the modulus `ε(δ) = C sqrt δ` supplied by `peres_theorem`; it tends to zero
at the origin and uniformly bounds every LTF. -/
theorem linearThreshold_uniformlyNoiseStable :
    IsUniformlyNoiseStable linearThresholdClass := by
  obtain ⟨C, hC0, hC⟩ := peres_theorem
  refine ⟨linearThresholdClass_isBooleanValued, fun δ ↦ min 1 (C * Real.sqrt δ), ?_, ?_, ?_⟩
  · intro δ hδ
    exact ⟨le_min zero_le_one (mul_nonneg hC0 (Real.sqrt_nonneg δ)), min_le_left _ _⟩
  · have hsqrt : Filter.Tendsto (fun δ : ℝ ↦ C * Real.sqrt δ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h : Filter.Tendsto Real.sqrt (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h0 := (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa using h0
      simpa using h.const_mul C
    simpa using (tendsto_const_nhds (x := (1 : ℝ))
      (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))).min hsqrt
  · intro n f hf δ hδ
    exact le_min (le_trans (noiseSensitivity_le_half hδ.2 f) (by norm_num)) (hC hf δ hδ)

/-! ## Polynomial threshold functions -/

/-- The polylogarithmic modulus appearing in Kane's bound tends to zero at the origin. -/
lemma tendsto_sqrt_mul_log_pow (d : ℕ) :
    Filter.Tendsto (fun δ : ℝ ↦ Real.sqrt δ * Real.log (1 / δ) ^ d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hlittle :=
    isLittleO_abs_log_rpow_rpow_nhdsGT_zero (s := (-(1 / 2) : ℝ)) (d : ℝ) (by norm_num)
  refine hlittle.tendsto_div_nhds_zero.congr' ?_
  have hmem : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ ∧ δ < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with δ h1 h2 using ⟨h1, h2⟩
  filter_upwards [hmem] with δ ⟨hδ0, hδ1⟩
  have hs : Real.sqrt δ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hδ0)
  have hlog : |Real.log δ| = Real.log (1 / δ) := by
    rw [abs_of_nonpos (Real.log_nonpos (le_of_lt hδ0) (le_of_lt hδ1)), one_div, Real.log_inv]
  have h1 : |Real.log δ| ^ (d : ℝ) = Real.log (1 / δ) ^ d := by
    rw [Real.rpow_natCast, hlog]
  have h2 : δ ^ (-(1 / 2) : ℝ) = (Real.sqrt δ)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hδ0), ← Real.sqrt_eq_rpow]
  rw [h1, h2]
  field_simp

/-- Kane's total-influence bound for polynomial threshold functions of degree at least two.

This is the external analytic input behind Theorem 5.37: Kane bounds the Gaussian surface area of a
degree-`k` polynomial threshold region and transfers the estimate to the discrete cube. Degrees
`k ≤ 1` need no external input, since a polynomial threshold function of degree at most one is a
linear threshold function and `ltf_totalInfluence_le_sqrt` applies; see
`kane_totalInfluence_le`, which upgrades this statement to all degrees.
[OD14, Thm. 5.37; Kan12] -/
theorem kane_totalInfluence_bound_of_two_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ), 2 ≤ k → ∀ f : BooleanFunc n,
      f ∈ polynomialThresholdClass k n →
        totalInfluence f ≤ Real.sqrt n *
          Real.rpow ((2 : ℝ) ^ k * Real.log (max n 2))
            (C * k * Real.log (max k 2)) := sorry

/-- A polynomial threshold function of degree at most one is a linear threshold function. -/
lemma isLinearThreshold_of_polynomialThresholdClass {n k : ℕ} (hk : k ≤ 1) {f : BooleanFunc n}
    (hf : f ∈ polynomialThresholdClass k n) : IsLinearThreshold f := by
  obtain ⟨-, p, hdeg, hrep⟩ := hf
  exact ⟨p, fun S hS ↦ hdeg S (lt_of_le_of_lt hk hS), hrep⟩

/-- Kane's total-influence bound, for every degree. The degrees `k ≤ 1` are proved here from the
linear-threshold bound; the remaining degrees are the external input
`kane_totalInfluence_bound_of_two_le`. [OD14, Thm. 5.37; Kan12] -/
theorem kane_totalInfluence_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (f : BooleanFunc n),
      f ∈ polynomialThresholdClass k n →
        totalInfluence f ≤ Real.sqrt n *
          Real.rpow ((2 : ℝ) ^ k * Real.log (max n 2))
            (C * k * Real.log (max k 2)) := by
  obtain ⟨C, hC, hKane⟩ := kane_totalInfluence_bound_of_two_le
  refine ⟨C, hC, ?_⟩
  intro n k f hf
  rcases le_or_gt 2 k with hk | hk
  · exact hKane n k hk f hf
  · have hk1 : k ≤ 1 := by omega
    have hinf : totalInfluence f ≤ Real.sqrt n :=
      ltf_totalInfluence_le_sqrt (isLinearThreshold_of_polynomialThresholdClass hk1 hf)
    have hfac : (1 : ℝ) ≤ Real.rpow ((2 : ℝ) ^ k * Real.log (max (n : ℝ) 2))
        (C * k * Real.log (max (k : ℝ) 2)) := by
      interval_cases k
      · simp
      · have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hlogn : Real.log 2 ≤ Real.log (max (n : ℝ) 2) :=
          Real.log_le_log (by norm_num) (le_max_right _ _)
        have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ (1 : ℕ) * Real.log (max (n : ℝ) 2) := by
          simp only [pow_one]
          nlinarith
        refine Real.one_le_rpow hbase ?_
        have hlogk : (0 : ℝ) ≤ Real.log (max ((1 : ℕ) : ℝ) 2) :=
          Real.log_nonneg (le_trans one_le_two (le_max_right _ _))
        positivity
    calc totalInfluence f ≤ Real.sqrt n := hinf
      _ = Real.sqrt n * 1 := (mul_one _).symm
      _ ≤ Real.sqrt n * Real.rpow ((2 : ℝ) ^ k * Real.log (max (n : ℝ) 2))
            (C * k * Real.log (max (k : ℝ) 2)) :=
          mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)

/-- The arithmetic estimate converting Kane's total-influence bound at `m = ⌊1/δ⌋` blocks into the
polylogarithmic noise-sensitivity bound. -/
lemma kane_noise_aux {k d : ℕ} {E δ : ℝ} (hE0 : 0 ≤ E) (hEd : E ≤ (d : ℝ))
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 1 / 2) (M : ℕ) (hM2 : 2 ≤ M) (hMδ : (M : ℝ) ≤ δ⁻¹)
    (hMlb : δ⁻¹ / 2 ≤ (M : ℝ)) :
    Real.sqrt M * Real.rpow ((2 : ℝ) ^ k * Real.log (max (M : ℝ) 2)) E / M
      ≤ Real.sqrt 2 * ((2 : ℝ) ^ k) ^ E * Real.log 2 ^ (-(d : ℝ)) * Real.sqrt δ
          * Real.log (1 / δ) ^ d := by
  have hM2R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hinv2 : (2 : ℝ) ≤ δ⁻¹ := le_trans hM2R hMδ
  set L : ℝ := Real.log (1 / δ) with hLdef
  have hLinv : L = Real.log δ⁻¹ := by rw [hLdef, one_div]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hL2 : Real.log 2 ≤ L := by
    rw [hLinv]
    exact Real.log_le_log (by norm_num) hinv2
  have hLpos : 0 < L := lt_of_lt_of_le hlog2pos hL2
  -- the base of the `rpow` is controlled by `log (1/δ)`
  have hlogM : Real.log (max (M : ℝ) 2) ≤ L := by
    rw [hLinv]
    exact Real.log_le_log (by positivity) (max_le hMδ hinv2)
  have hlogMnn : (0 : ℝ) ≤ Real.log (max (M : ℝ) 2) :=
    Real.log_nonneg (le_trans one_le_two (le_max_right _ _))
  have hb0 : (0 : ℝ) ≤ (2 : ℝ) ^ k * Real.log (max (M : ℝ) 2) := by positivity
  have hstep1 : Real.rpow ((2 : ℝ) ^ k * Real.log (max (M : ℝ) 2)) E ≤ ((2 : ℝ) ^ k * L) ^ E :=
    Real.rpow_le_rpow hb0 (mul_le_mul_of_nonneg_left hlogM (by positivity)) hE0
  have hstep2 : ((2 : ℝ) ^ k * L) ^ E = ((2 : ℝ) ^ k) ^ E * L ^ E :=
    Real.mul_rpow (by positivity) hLpos.le
  have hK1 : (1 : ℝ) ≤ Real.log 2 ^ (-(d : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlog2pos hlog2le1
      (neg_nonpos.mpr (Nat.cast_nonneg d))
  have hKpos : (0 : ℝ) < Real.log 2 ^ (-(d : ℝ)) := lt_of_lt_of_le zero_lt_one hK1
  have hstep3 : L ^ E ≤ Real.log 2 ^ (-(d : ℝ)) * L ^ d := by
    rcases le_or_gt 1 L with hL1 | hL1
    · have h1 : L ^ E ≤ L ^ ((d : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 hEd
      have h2 : L ^ ((d : ℝ)) = L ^ d := Real.rpow_natCast L d
      have h3 : (0 : ℝ) ≤ L ^ d := by positivity
      nlinarith
    · have h1 : L ^ E ≤ L ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hLpos hL1.le hE0
      rw [Real.rpow_zero L] at h1
      have h3 : Real.log 2 ^ d ≤ L ^ d := pow_le_pow_left₀ hlog2pos.le hL2 d
      have h4 : Real.log 2 ^ (-(d : ℝ)) * Real.log 2 ^ (d : ℝ) = 1 := by
        rw [← Real.rpow_add hlog2pos]
        simp
      rw [Real.rpow_natCast (Real.log 2) d] at h4
      have h6 : Real.log 2 ^ (-(d : ℝ)) * Real.log 2 ^ d
          ≤ Real.log 2 ^ (-(d : ℝ)) * L ^ d := mul_le_mul_of_nonneg_left h3 hKpos.le
      rw [h4] at h6
      linarith
  have hsqrtM : Real.sqrt M * Real.sqrt M = (M : ℝ) := Real.mul_self_sqrt hMpos.le
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have h2dM : (1 : ℝ) ≤ 2 * δ * M := by
    have hid : δ * δ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hδ0)
    nlinarith [hMlb, hδ0]
  have hkey : (1 : ℝ) ≤ Real.sqrt 2 * Real.sqrt δ * Real.sqrt M := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_mul (by positivity)]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (2 * δ * M) := Real.sqrt_le_sqrt h2dM
  have hstep4 : Real.sqrt M / M ≤ Real.sqrt 2 * Real.sqrt δ := by
    rw [div_le_iff₀ hMpos]
    nlinarith [hkey, Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg δ, hsM]
  have hBnn : (0 : ℝ) ≤ Real.rpow ((2 : ℝ) ^ k * Real.log (max (M : ℝ) 2)) E :=
    Real.rpow_nonneg hb0 E
  have hcomb : Real.rpow ((2 : ℝ) ^ k * Real.log (max (M : ℝ) 2)) E
      ≤ ((2 : ℝ) ^ k) ^ E * (Real.log 2 ^ (-(d : ℝ)) * L ^ d) := by
    refine le_trans hstep1 ?_
    rw [hstep2]
    exact mul_le_mul_of_nonneg_left hstep3 (Real.rpow_nonneg (by positivity) E)
  have hrhs0 : (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ E * (Real.log 2 ^ (-(d : ℝ)) * L ^ d) := by
    have h1 : (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ E := Real.rpow_nonneg (by positivity) E
    have h2 : (0 : ℝ) ≤ L ^ d := by positivity
    nlinarith
  have hdiv0 : (0 : ℝ) ≤ Real.sqrt M / M := by positivity
  have hfinal := mul_le_mul hcomb hstep4 hdiv0 hrhs0
  calc Real.sqrt M * Real.rpow ((2 : ℝ) ^ k * Real.log (max (M : ℝ) 2)) E / M
      = Real.rpow ((2 : ℝ) ^ k * Real.log (max (M : ℝ) 2)) E * (Real.sqrt M / M) := by ring
    _ ≤ ((2 : ℝ) ^ k) ^ E * (Real.log 2 ^ (-(d : ℝ)) * L ^ d) * (Real.sqrt 2 * Real.sqrt δ) :=
        hfinal
    _ = Real.sqrt 2 * ((2 : ℝ) ^ k) ^ E * Real.log 2 ^ (-(d : ℝ)) * Real.sqrt δ * L ^ d := by ring

/-- Degree-`k` polynomial threshold functions satisfy Kane's total-influence bound. The universal
constant `C` makes the exponent hidden by `O(k log k)` explicit; `max n 2` and `max k 2` give a
nondegenerate total extension at the small endpoint values. The second conjunct records the
polylogarithmic noise-sensitivity consequence for every fixed positive degree.
[OD14, Thm. 5.37; Kan12]

**Proof sketch.** Kane bounds the Gaussian surface area of a degree-`k` polynomial threshold region
and transfers the estimate to the discrete cube. Applying `influence_bound_implies_noise_bound` at
`m = ⌊1/δ⌋` converts the total-influence estimate into the displayed noise-sensitivity bound. -/
theorem kane_totalInfluence_bound :
    (∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (f : BooleanFunc n),
      f ∈ polynomialThresholdClass k n →
        totalInfluence f ≤ Real.sqrt n *
          Real.rpow ((2 : ℝ) ^ k * Real.log (max n 2))
            (C * k * Real.log (max k 2))) ∧
    (∀ k : ℕ, 0 < k → ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧ ∀ {n : ℕ} {f : BooleanFunc n},
      f ∈ polynomialThresholdClass k n → ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
        noiseSensitivity δ f ≤
          C * Real.sqrt δ * Real.log (1 / δ) ^ d) := by
  refine ⟨kane_totalInfluence_le, ?_⟩
  intro k hk
  obtain ⟨C₀, hC₀, hKane⟩ := kane_totalInfluence_le
  set E : ℝ := C₀ * k * Real.log (max (k : ℝ) 2) with hEdef
  have hlogk : 0 ≤ Real.log (max (k : ℝ) 2) :=
    Real.log_nonneg (le_trans one_le_two (le_max_right _ _))
  have hE0 : 0 ≤ E := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [hEdef]
    positivity
  set d : ℕ := ⌈E⌉₊ with hddef
  have hEd : E ≤ (d : ℝ) := Nat.le_ceil E
  set A : ℕ → ℝ := fun m ↦ Real.sqrt m *
    Real.rpow ((2 : ℝ) ^ k * Real.log (max (m : ℝ) 2)) E with hAdef
  refine ⟨Real.sqrt 2 * ((2 : ℝ) ^ k) ^ E * Real.log 2 ^ (-(d : ℝ)), d, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ((2 : ℝ) ^ k) ^ E := Real.rpow_nonneg (by positivity) E
    have h2 : (0 : ℝ) ≤ Real.log 2 ^ (-(d : ℝ)) := Real.rpow_nonneg (Real.log_nonneg one_le_two) _
    positivity
  · intro n f hf δ hδ
    obtain ⟨hδ0, hδ2⟩ := hδ
    have hbase := influence_bound_implies_noise_bound (polynomialThresholdClass k) A
      (fun hg ↦ hg.1) (polynomialThresholdClass_closed k)
      (fun {m} {g} hg ↦ hKane m k g hg) ⟨hδ0, hδ2⟩ hf
    set M : ℕ := noiseBlockCount δ with hMdef
    have hinv2 : (2 : ℝ) ≤ δ⁻¹ := by
      have h := inv_anti₀ hδ0 hδ2
      norm_num at h
      linarith
    have hM2 : 2 ≤ M := by
      rw [hMdef, noiseBlockCount]
      exact Nat.le_floor (by exact_mod_cast hinv2)
    have hMδ : (M : ℝ) ≤ δ⁻¹ := by
      rw [hMdef, noiseBlockCount]
      exact Nat.floor_le (by positivity)
    have hfloor : δ⁻¹ < (M : ℝ) + 1 := by
      rw [hMdef, noiseBlockCount]
      exact Nat.lt_floor_add_one _
    have hM2R : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    have hMlb : δ⁻¹ / 2 ≤ (M : ℝ) := by linarith
    exact le_trans hbase (kane_noise_aux hE0 hEd hδ0 hδ2 M hM2 hMδ hMlb)

/-- For each fixed degree, polynomial threshold functions form a uniformly noise-stable class.
[OD14, §5.5, consequence of Thm. 5.37]

**Proof sketch.** The polylogarithmic bound in `kane_totalInfluence_bound` tends to zero as the
noise rate tends to zero and is uniform over the input dimension. -/
theorem polynomialThreshold_uniformlyNoiseStable (k : ℕ) :
    IsUniformlyNoiseStable (polynomialThresholdClass k) := by
  obtain ⟨C, d, hC0, hC⟩ :=
    kane_totalInfluence_bound.2 (max k 1) (lt_of_lt_of_le Nat.zero_lt_one (le_max_right k 1))
  refine ⟨fun hf ↦ hf.1, fun δ ↦ min 1 (C * Real.sqrt δ * Real.log (1 / δ) ^ d), ?_, ?_, ?_⟩
  · intro δ hδ
    refine ⟨le_min zero_le_one ?_, min_le_left _ _⟩
    rcases eq_or_lt_of_le hδ.1 with h | h
    · rw [← h]
      simp
    · have hlog : 0 ≤ Real.log (1 / δ) :=
        Real.log_nonneg (by rw [le_div_iff₀ h]; linarith [hδ.2])
      exact mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg δ)) (pow_nonneg hlog d)
  · have h2 : Filter.Tendsto (fun δ : ℝ ↦ C * Real.sqrt δ * Real.log (1 / δ) ^ d)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa [mul_assoc] using (tendsto_sqrt_mul_log_pow d).const_mul C
    simpa using (tendsto_const_nhds (x := (1 : ℝ))
      (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))).min h2
  · intro n f hf δ hδ
    exact le_min (le_trans (noiseSensitivity_le_half hδ.2 f) (by norm_num))
      (hC (polynomialThresholdClass_mono (le_max_left k 1) n hf) δ hδ)

end ThresholdFunctions
end BooleanAnalysis
