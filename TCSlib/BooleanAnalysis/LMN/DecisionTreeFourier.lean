import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.Switching.Circuit

/-!
# Decision Trees and the Fourier Spectrum (O'Donnell Proposition 3.16)

Let `f : {0,1}ⁿ → {-1,1}` be computed by a decision tree `T` of size `s`
(number of leaves) and depth `k`. Then:

* `degree_le_depth`: `deg(f) ≤ k`;
* `sparsity_le`: `|{S : f̂(S) ≠ 0}| ≤ s·2^k` (and `s ≤ 2^k`, so `≤ 4^k`);
* `spectral_one_norm_le`: `‖f̂‖₁ = ∑_S |f̂(S)| ≤ s`;
* `fourierCoeff_granular`: every `f̂(S)` is an integer multiple of `2⁻ᵏ`.

The engine is a single structural induction: `DecisionTree.coeffs` recursively
computes the Fourier expansion of the ±1-encoded tree function, using the
identity (for a tree branching on variable `i` into `lo`/`hi`)

  `f = (f_lo + f_hi)/2 + χ_i · (f_lo − f_hi)/2`

together with `χ_i · χ_S = χ_{S ∆ {i}}`. All four bullets are read off the
recursion; sparsity follows from granularity + the 1-norm bound (each nonzero
coefficient has magnitude ≥ 2⁻ᵏ).

`degree_le_dtDepth` restates the degree bound for `dtDepth` (minimum decision-
tree depth), the form needed by the restriction ⇒ Fourier-concentration
transfer (O'Donnell Lemma 4.21) in the LMN pipeline.
-/

open BooleanAnalysis

namespace DecisionTree

variable {n : ℕ}

/-! ## Size, sign-encoding, and the coefficient recursion -/

/-- The size of a decision tree = number of leaves. -/
def size : DecisionTree n → ℕ
  | .leaf _ => 1
  | .branch _ lo hi => lo.size + hi.size

/-- The ±1-valued function computed by a decision tree
    (`false ↦ 1`, `true ↦ -1`, following `boolToSign`). -/
noncomputable def signEval (T : DecisionTree n) : BooleanFunc n :=
  fun x => boolToSign (T.eval x)

/-- The Fourier coefficients of `signEval`, computed by structural recursion.
    A branch on variable `i` satisfies `f = (f_lo + f_hi)/2 + χ_i (f_lo − f_hi)/2`,
    and multiplication by `χ_i` shifts frequency `S` to `S ∆ {i}`. -/
noncomputable def coeffs : DecisionTree n → Finset (Fin n) → ℝ
  | .leaf b, S => if S = ∅ then boolToSign b else 0
  | .branch i lo hi, S =>
      (coeffs lo S + coeffs hi S) / 2
        + (coeffs lo (symmDiff S {i}) - coeffs hi (symmDiff S {i})) / 2

/-! ## symmDiff helpers -/

private lemma symmDiff_singleton_invol (i : Fin n) :
    Function.Involutive (fun S : Finset (Fin n) => symmDiff S {i}) := fun S => by
  simp only [symmDiff_assoc, symmDiff_self, symmDiff_bot]

/-- Reindexing a sum over all frequencies by the involution `S ↦ S ∆ {i}`. -/
private lemma sum_symmDiff_reindex (g : Finset (Fin n) → ℝ) (i : Fin n) :
    ∑ S : Finset (Fin n), g (symmDiff S {i}) = ∑ S : Finset (Fin n), g S :=
  Fintype.sum_bijective _ ((symmDiff_singleton_invol i).bijective) _ _ (fun _ => rfl)

private lemma chiS_symmDiff_singleton (S : Finset (Fin n)) (i : Fin n) (x : BoolCube n) :
    chiS (symmDiff S {i}) x = chiS S x * boolToSign (x i) := by
  rw [← chiS_mul_chiS, chiS_singleton]

private lemma card_symmDiff_singleton (S : Finset (Fin n)) (i : Fin n) :
    S.card - 1 ≤ (symmDiff S {i}).card := by
  by_cases h : i ∈ S
  · have he : symmDiff S {i} = S.erase i := by
      ext j
      by_cases hj : j = i <;>
        simp [Finset.mem_symmDiff, Finset.mem_erase, hj, h]
    rw [he, Finset.card_erase_of_mem h]
  · have he : symmDiff S {i} = insert i S := by
      ext j
      by_cases hj : j = i <;>
        simp [Finset.mem_symmDiff, Finset.mem_insert, hj, h]
    rw [he, Finset.card_insert_of_notMem h]
    omega

/-! ## The representation lemma -/

/-- `signEval T = ∑_S coeffs T S · χ_S` pointwise. -/
lemma signEval_eq_sum_coeffs (T : DecisionTree n) (x : BoolCube n) :
    T.signEval x = ∑ S : Finset (Fin n), T.coeffs S * chiS S x := by
  induction T with
  | leaf b =>
      simp [signEval, DecisionTree.eval, coeffs, ite_mul, Finset.sum_ite_eq', chiS_empty]
  | branch i lo hi ih_lo ih_hi =>
      have expand : ∑ S : Finset (Fin n), (DecisionTree.branch i lo hi).coeffs S * chiS S x
          = ((∑ S : Finset (Fin n), lo.coeffs S * chiS S x)
              + ∑ S : Finset (Fin n), hi.coeffs S * chiS S x) / 2
            + ((∑ S : Finset (Fin n), lo.coeffs S * chiS S x)
              - ∑ S : Finset (Fin n), hi.coeffs S * chiS S x) / 2 * boolToSign (x i) := by
        have step1 : ∑ S : Finset (Fin n), (DecisionTree.branch i lo hi).coeffs S * chiS S x
            = (∑ S : Finset (Fin n), (lo.coeffs S + hi.coeffs S) / 2 * chiS S x)
              + ∑ S : Finset (Fin n),
                (lo.coeffs (symmDiff S {i}) - hi.coeffs (symmDiff S {i})) / 2 * chiS S x := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun S _ => ?_
          simp only [coeffs]; ring
        have step2 : ∑ S : Finset (Fin n),
              (lo.coeffs (symmDiff S {i}) - hi.coeffs (symmDiff S {i})) / 2 * chiS S x
            = ∑ S : Finset (Fin n),
              (lo.coeffs S - hi.coeffs S) / 2 * chiS S x * boolToSign (x i) := by
          rw [← sum_symmDiff_reindex
            (fun S => (lo.coeffs S - hi.coeffs S) / 2 * chiS S x * boolToSign (x i)) i]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [chiS_symmDiff_singleton]
          cases x i <;> simp [boolToSign]
        have hA : ∑ S : Finset (Fin n), (lo.coeffs S + hi.coeffs S) / 2 * chiS S x
            = ((∑ S : Finset (Fin n), lo.coeffs S * chiS S x)
                + ∑ S : Finset (Fin n), hi.coeffs S * chiS S x) / 2 := by
          have hterm : ∀ S : Finset (Fin n), (lo.coeffs S + hi.coeffs S) / 2 * chiS S x
              = (lo.coeffs S * chiS S x + hi.coeffs S * chiS S x) / 2 := fun S => by ring
          rw [Finset.sum_congr rfl fun S _ => hterm S, ← Finset.sum_div,
            Finset.sum_add_distrib]
        have hB : ∑ S : Finset (Fin n),
              (lo.coeffs S - hi.coeffs S) / 2 * chiS S x * boolToSign (x i)
            = ((∑ S : Finset (Fin n), lo.coeffs S * chiS S x)
                - ∑ S : Finset (Fin n), hi.coeffs S * chiS S x) / 2 * boolToSign (x i) := by
          rw [← Finset.sum_mul]
          congr 1
          have hterm : ∀ S : Finset (Fin n), (lo.coeffs S - hi.coeffs S) / 2 * chiS S x
              = (lo.coeffs S * chiS S x - hi.coeffs S * chiS S x) / 2 := fun S => by ring
          rw [Finset.sum_congr rfl fun S _ => hterm S, ← Finset.sum_div,
            Finset.sum_sub_distrib]
        rw [step1, step2, hA, hB]
      rw [expand, ← ih_lo, ← ih_hi]
      simp only [signEval, DecisionTree.eval]
      cases hxi : x i <;> simp [boolToSign] <;> ring

/-! ## The four properties of the coefficient recursion -/

/-- Frequencies above the depth carry no Fourier weight. -/
lemma coeffs_eq_zero_of_depth_lt (T : DecisionTree n) (S : Finset (Fin n))
    (h : T.depth < S.card) : T.coeffs S = 0 := by
  induction T generalizing S with
  | leaf b =>
      have hS : S ≠ ∅ := by
        intro hS
        rw [hS] at h
        simp [DecisionTree.depth] at h
      simp [coeffs, hS]
  | branch i lo hi ih_lo ih_hi =>
      simp only [DecisionTree.depth] at h
      have hSi := card_symmDiff_singleton S i
      rw [coeffs, ih_lo _ (by omega), ih_hi _ (by omega),
        ih_lo _ (by omega), ih_hi _ (by omega)]
      ring

/-- The spectral 1-norm of the coefficients is at most the number of leaves. -/
lemma sum_abs_coeffs_le (T : DecisionTree n) :
    ∑ S : Finset (Fin n), |T.coeffs S| ≤ (T.size : ℝ) := by
  induction T with
  | leaf b =>
      have habs : ∀ S : Finset (Fin n),
          |(DecisionTree.leaf b : DecisionTree n).coeffs S|
            = if S = ∅ then 1 else 0 := by
        intro S
        simp only [coeffs]
        split_ifs <;> cases b <;> simp [boolToSign]
      rw [Finset.sum_congr rfl fun S _ => habs S]
      simp [size, Finset.sum_ite_eq']
  | branch i lo hi ih_lo ih_hi =>
      have hbound : ∀ S : Finset (Fin n),
          |(DecisionTree.branch i lo hi).coeffs S|
            ≤ (|lo.coeffs S| + |hi.coeffs S|) / 2
              + (|lo.coeffs (symmDiff S {i})| + |hi.coeffs (symmDiff S {i})|) / 2 := by
        intro S
        simp only [coeffs]
        have h₁ := le_abs_self (lo.coeffs S)
        have h₂ := neg_abs_le (lo.coeffs S)
        have h₃ := le_abs_self (hi.coeffs S)
        have h₄ := neg_abs_le (hi.coeffs S)
        have h₅ := le_abs_self (lo.coeffs (symmDiff S {i}))
        have h₆ := neg_abs_le (lo.coeffs (symmDiff S {i}))
        have h₇ := le_abs_self (hi.coeffs (symmDiff S {i}))
        have h₈ := neg_abs_le (hi.coeffs (symmDiff S {i}))
        rw [abs_le]
        constructor <;> linarith
      calc ∑ S : Finset (Fin n), |(DecisionTree.branch i lo hi).coeffs S|
          ≤ ∑ S : Finset (Fin n),
              ((|lo.coeffs S| + |hi.coeffs S|) / 2
                + (|lo.coeffs (symmDiff S {i})| + |hi.coeffs (symmDiff S {i})|) / 2) :=
            Finset.sum_le_sum fun S _ => hbound S
        _ = (∑ S : Finset (Fin n), (|lo.coeffs S| + |hi.coeffs S|) / 2)
              + ∑ S : Finset (Fin n),
                (|lo.coeffs (symmDiff S {i})| + |hi.coeffs (symmDiff S {i})|) / 2 :=
            Finset.sum_add_distrib
        _ = (∑ S : Finset (Fin n), (|lo.coeffs S| + |hi.coeffs S|) / 2)
              + ∑ S : Finset (Fin n), (|lo.coeffs S| + |hi.coeffs S|) / 2 := by
            rw [sum_symmDiff_reindex (fun S => (|lo.coeffs S| + |hi.coeffs S|) / 2) i]
        _ = (∑ S : Finset (Fin n), |lo.coeffs S|)
              + ∑ S : Finset (Fin n), |hi.coeffs S| := by
            rw [← Finset.sum_div, Finset.sum_add_distrib]
            ring
        _ ≤ (lo.size : ℝ) + (hi.size : ℝ) := add_le_add ih_lo ih_hi
        _ = ((DecisionTree.branch i lo hi).size : ℝ) := by
            simp [size]

/-- Granularity, multiplicative form: `coeffs T S · 2ᵏ ∈ ℤ` whenever `T.depth ≤ k`. -/
lemma coeffs_mul_two_pow_int (T : DecisionTree n) (k : ℕ) (hk : T.depth ≤ k)
    (S : Finset (Fin n)) : ∃ m : ℤ, T.coeffs S * 2 ^ k = (m : ℝ) := by
  induction T generalizing k S with
  | leaf b =>
      refine ⟨if S = ∅ then (if b then -(2 ^ k) else 2 ^ k) else 0, ?_⟩
      simp only [coeffs, boolToSign]
      split_ifs <;> push_cast <;> ring
  | branch i lo hi ih_lo ih_hi =>
      have hk1 : 1 ≤ k := by
        refine le_trans ?_ hk
        simp [DecisionTree.depth]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [DecisionTree.depth] at hk
      obtain ⟨m₁, h₁⟩ := ih_lo k' (by omega) S
      obtain ⟨m₂, h₂⟩ := ih_hi k' (by omega) S
      obtain ⟨m₃, h₃⟩ := ih_lo k' (by omega) (symmDiff S {i})
      obtain ⟨m₄, h₄⟩ := ih_hi k' (by omega) (symmDiff S {i})
      refine ⟨m₁ + m₂ + m₃ - m₄, ?_⟩
      simp only [coeffs]
      push_cast
      rw [pow_succ]
      linear_combination h₁ + h₂ + h₃ - h₄

/-- Granularity: every coefficient is an integer multiple of `2^{-depth}`. -/
lemma coeffs_granular (T : DecisionTree n) (S : Finset (Fin n)) :
    ∃ m : ℤ, T.coeffs S = (m : ℝ) / 2 ^ T.depth := by
  obtain ⟨m, hm⟩ := coeffs_mul_two_pow_int T T.depth le_rfl S
  exact ⟨m, by rw [eq_div_iff (by positivity : ((2 : ℝ) ^ T.depth) ≠ 0)]; exact hm⟩

/-- A tree with depth `k` has at most `2^k` leaves. -/
lemma size_le_two_pow_depth (T : DecisionTree n) : T.size ≤ 2 ^ T.depth := by
  induction T with
  | leaf b => simp [size, DecisionTree.depth]
  | branch i lo hi ih_lo ih_hi =>
      have hlo : 2 ^ lo.depth ≤ 2 ^ max lo.depth hi.depth :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hhi : 2 ^ hi.depth ≤ 2 ^ max lo.depth hi.depth :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      simp only [size, DecisionTree.depth]
      calc lo.size + hi.size ≤ 2 ^ max lo.depth hi.depth + 2 ^ max lo.depth hi.depth := by
            omega
        _ = 2 ^ (1 + max lo.depth hi.depth) := by
            rw [Nat.add_comm 1, Nat.pow_succ]
            ring

/-! ## From representations to Fourier coefficients -/

/-- The Fourier coefficient of an explicit character combination reads off the
    coefficient (uniqueness of the Fourier expansion). -/
lemma fourierCoeff_sum_chiS (c : Finset (Fin n) → ℝ) (T : Finset (Fin n)) :
    fourierCoeff (fun x => ∑ S : Finset (Fin n), c S * chiS S x) T = c T := by
  have expand : fourierCoeff (fun x => ∑ S : Finset (Fin n), c S * chiS S x) T
      = ∑ S : Finset (Fin n), c S * innerProduct (chiS S) (chiS T) := by
    show uniformWeight n * ∑ x : BoolCube n,
        (∑ S : Finset (Fin n), c S * chiS S x) * chiS T x
      = ∑ S : Finset (Fin n),
          c S * (uniformWeight n * ∑ x : BoolCube n, chiS S x * chiS T x)
    calc uniformWeight n * ∑ x : BoolCube n,
            (∑ S : Finset (Fin n), c S * chiS S x) * chiS T x
        = uniformWeight n * ∑ x : BoolCube n,
            ∑ S : Finset (Fin n), c S * (chiS S x * chiS T x) := by
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun S _ => by ring
      _ = uniformWeight n * ∑ S : Finset (Fin n),
            ∑ x : BoolCube n, c S * (chiS S x * chiS T x) := by
          rw [Finset.sum_comm]
      _ = ∑ S : Finset (Fin n),
            c S * (uniformWeight n * ∑ x : BoolCube n, chiS S x * chiS T x) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [← Finset.mul_sum]
          ring
  rw [expand]
  have hterm : ∀ S : Finset (Fin n),
      c S * innerProduct (chiS S) (chiS T) = if S = T then c S else 0 := by
    intro S
    rw [BooleanAnalysis.fourier_coeff_chi]
    split_ifs <;> simp
  simp only [hterm]
  simp

/-- The Fourier coefficients of the tree function are exactly `T.coeffs`. -/
theorem fourierCoeff_signEval (T : DecisionTree n) (S : Finset (Fin n)) :
    fourierCoeff T.signEval S = T.coeffs S := by
  have hrepr : T.signEval = fun x => ∑ S : Finset (Fin n), T.coeffs S * chiS S x :=
    funext fun x => signEval_eq_sum_coeffs T x
  rw [hrepr, fourierCoeff_sum_chiS]

/-! ## O'Donnell Proposition 3.16 -/

/-- **Proposition 3.16, degree bound**: a function computed by a decision tree
    of depth `k` has Fourier degree at most `k`. -/
theorem degree_le_depth (T : DecisionTree n) :
    has_degree_at_most T.signEval T.depth := by
  intro S hS
  by_contra hcard
  push_neg at hcard
  exact hS (by rw [fourierCoeff_signEval]; exact coeffs_eq_zero_of_depth_lt T S hcard)

/-- **Proposition 3.16, spectral 1-norm bound**: `‖f̂‖₁ ≤ s` (the tree size);
    here `‖f‖∞ = 1` since `f` is ±1-valued. -/
theorem spectral_one_norm_le (T : DecisionTree n) :
    ∑ S : Finset (Fin n), |fourierCoeff T.signEval S| ≤ (T.size : ℝ) := by
  calc ∑ S : Finset (Fin n), |fourierCoeff T.signEval S|
      = ∑ S : Finset (Fin n), |T.coeffs S| :=
        Finset.sum_congr rfl fun S _ => by rw [fourierCoeff_signEval]
    _ ≤ (T.size : ℝ) := sum_abs_coeffs_le T

/-- **Proposition 3.16, granularity**: every `f̂(S)` is an integer multiple
    of `2^{-k}` where `k` is the tree depth. -/
theorem fourierCoeff_granular (T : DecisionTree n) (S : Finset (Fin n)) :
    ∃ m : ℤ, fourierCoeff T.signEval S = (m : ℝ) / 2 ^ T.depth := by
  rw [fourierCoeff_signEval]
  exact coeffs_granular T S

/-- **Proposition 3.16, sparsity**: the Fourier support has size at most
    `s · 2^k`. Follows from granularity (each nonzero coefficient has magnitude
    `≥ 2^{-k}`) and the spectral 1-norm bound. -/
theorem sparsity_le (T : DecisionTree n) :
    (Finset.univ.filter fun S : Finset (Fin n) =>
      fourierCoeff T.signEval S ≠ 0).card ≤ T.size * 2 ^ T.depth := by
  classical
  set F := Finset.univ.filter fun S : Finset (Fin n) =>
    fourierCoeff T.signEval S ≠ 0 with hF
  have hlow : ∀ S ∈ F, 1 / (2 : ℝ) ^ T.depth ≤ |fourierCoeff T.signEval S| := by
    intro S hS
    obtain ⟨m, hm⟩ := fourierCoeff_granular T S
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0] at hm
      simp only [Int.cast_zero, zero_div] at hm
      exact (Finset.mem_filter.mp hS).2 hm
    rw [hm, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ T.depth)]
    gcongr
    exact_mod_cast Int.one_le_abs hm0
  have hcard : (F.card : ℝ) * (1 / (2 : ℝ) ^ T.depth) ≤ (T.size : ℝ) := by
    calc (F.card : ℝ) * (1 / (2 : ℝ) ^ T.depth)
        = F.card • (1 / (2 : ℝ) ^ T.depth) := by rw [nsmul_eq_mul]
      _ ≤ ∑ S ∈ F, |fourierCoeff T.signEval S| := Finset.card_nsmul_le_sum F _ _ hlow
      _ ≤ ∑ S : Finset (Fin n), |fourierCoeff T.signEval S| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => abs_nonneg _)
      _ ≤ (T.size : ℝ) := spectral_one_norm_le T
  have hreal : (F.card : ℝ) ≤ (T.size : ℝ) * 2 ^ T.depth := by
    rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ T.depth)] at hcard
    exact hcard
  exact_mod_cast hreal

/-- Sparsity, absolute form: the Fourier support has size at most `4^k`. -/
theorem sparsity_le_four_pow (T : DecisionTree n) :
    (Finset.univ.filter fun S : Finset (Fin n) =>
      fourierCoeff T.signEval S ≠ 0).card ≤ 4 ^ T.depth := by
  calc (Finset.univ.filter fun S : Finset (Fin n) =>
        fourierCoeff T.signEval S ≠ 0).card
      ≤ T.size * 2 ^ T.depth := sparsity_le T
    _ ≤ 2 ^ T.depth * 2 ^ T.depth :=
        Nat.mul_le_mul_right _ (size_le_two_pow_depth T)
    _ = 4 ^ T.depth := by
        rw [← Nat.mul_pow]

/-! ## The `dtDepth` form (interface for O'Donnell Lemma 4.21) -/

/-- Specification of `dtDepth`: some tree of depth `≤ dtDepth f` computes `f`. -/
lemma exists_dtree_of_dtDepth (f : (Fin n → Bool) → Bool) :
    ∃ T : DecisionTree n, T.depth ≤ dtDepth f ∧ ∀ x, T.eval x = f x := by
  classical
  unfold dtDepth
  exact Nat.find_spec
    (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x) _

/-- **Proposition 3.16 for `dtDepth`**: the ±1-encoding of a Boolean function
    has Fourier degree at most its minimum decision-tree depth. This is the
    "DT(f) ≤ k ⇒ deg(f) ≤ k" input to O'Donnell Lemma 4.21. -/
theorem degree_le_dtDepth (f : (Fin n → Bool) → Bool) :
    has_degree_at_most (fun x => boolToSign (f x)) (dtDepth f) := by
  obtain ⟨T, hdepth, heval⟩ := exists_dtree_of_dtDepth f
  have hfun : (fun x => boolToSign (f x)) = T.signEval := by
    funext x
    rw [signEval, heval x]
  rw [hfun]
  intro S hS
  exact le_trans (degree_le_depth T S hS) hdepth

end DecisionTree
