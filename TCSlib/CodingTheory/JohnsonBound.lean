

import Mathlib


noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset

namespace CodingTheory

namespace Johnson

abbrev BitVec (n : ℕ) := Fin n → Bool

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

def wt {n : ℕ} (x : BitVec n) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

def hdist {n : ℕ} (x y : BitVec n) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

def pmOne {n : ℕ} (x : BitVec n) : Euc n :=
  fun i => if x i then (-1 : ℝ) else (1 : ℝ)

def ones {n : ℕ} : Euc n :=
  fun _ => (1 : ℝ)

def shifted {n : ℕ} (α : ℝ) (x : BitVec n) : Euc n :=
  pmOne x - α • ones

def normalize {n : ℕ} (u : Euc n) : Euc n :=
  (‖u‖)⁻¹ • u

@[simp] lemma ones_apply {n : ℕ} (i : Fin n) : ones (n := n) i = (1 : ℝ) := rfl

@[simp] lemma pmOne_apply_false {n : ℕ} (x : BitVec n) (i : Fin n) (h : x i = false) :
    pmOne x i = (1 : ℝ) := by
  simp [pmOne, h]

@[simp] lemma pmOne_apply_true {n : ℕ} (x : BitVec n) (i : Fin n) (h : x i = true) :
    pmOne x i = (-1 : ℝ) := by
  simp [pmOne, h]

def J2 (n d : ℕ) : ℝ :=
  (((n : ℝ) - Real.sqrt ((n : ℝ) * ((n : ℝ) - 2 * (d : ℝ)))) / 2)

def alpha (n d : ℕ) : ℝ :=
  Real.sqrt ((((n : ℝ) - 2 * (d : ℝ)) / (n : ℝ)))

def AdmissibleCode (n d w : ℕ) (C : Finset (BitVec n)) : Prop :=
  (∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hdist x y) ∧
  (∀ x ∈ C, wt x ≤ w)

lemma coord_mul_pmOne {n : ℕ} (x y : BitVec n) (i : Fin n) :
    (pmOne x i) * (pmOne y i) = if x i = y i then (1 : ℝ) else (-1 : ℝ) := by
  by_cases hx : x i <;> by_cases hy : y i <;> simp [pmOne, hx, hy]

lemma inner_pmOne_pmOne {n : ℕ} (x y : BitVec n) :
    ⟪pmOne x, pmOne y⟫_[ℝ] = (n : ℝ) - 2 * (hdist x y : ℝ) := by
  have h_pmOne : ∀ i, (pmOne x i) * (pmOne y i) = if x i = y i then 1 else -1 := by
    exact fun i => coord_mul_pmOne x y i;
  have h_hdist : (CodingTheory.Johnson.hdist x y : ℝ) = ∑ i, (if x i ≠ y i then 1 else 0) := by
    simp +decide [ Finset.sum_ite, Finset.filter_congr, Finset.filter_ne ];
    exact congr_arg Finset.card ( Finset.filter_congr fun _ _ => by aesop );
  simp_all +decide [ RCLike.wInner ];
  simp_all +decide [ mul_comm, Finset.sum_ite ];
  rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num ; ring;
  rw [ Nat.cast_sub ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring

lemma inner_pmOne_ones {n : ℕ} (x : BitVec n) :
    ⟪pmOne x, ones⟫_[ℝ] = (n : ℝ) - 2 * (wt x : ℝ) := by
  have h_inner_expanded : RCLike.wInner 1 (CodingTheory.Johnson.pmOne x) CodingTheory.Johnson.ones = ∑ i, (pmOne x i) * (ones i) := by
    simp [RCLike.wInner];
  have h_sum_simplified : ∑ i, (pmOne x i) * (ones i) = ∑ i, (if x i then -1 else 1 : ℝ) := by
    exact Finset.sum_congr rfl fun i _ => by unfold CodingTheory.Johnson.pmOne CodingTheory.Johnson.ones; aesop;
  simp_all +decide [ Finset.sum_ite ];
  rw [ show ( Finset.univ.filter fun i => x i = Bool.false ) = Finset.univ \ ( Finset.univ.filter fun i => x i = Bool.true ) by ext; aesop, Finset.card_sdiff ] ; norm_num ; ring!;
  rw [ Nat.cast_sub ( show _ ≤ _ from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring;

lemma inner_ones_ones {n : ℕ} :
    ⟪ones (n := n), ones (n := n)⟫_[ℝ] = (n : ℝ) := by
  simp [RCLike.wInner, ones]

lemma inner_shifted_expand {n : ℕ} (α : ℝ) (x y : BitVec n) :
    ⟪shifted α x, shifted α y⟫_[ℝ]
      = ⟪pmOne x, pmOne y⟫_[ℝ]
        - α * ⟪pmOne x, ones (n := n)⟫_[ℝ]
        - α * ⟪pmOne y, ones (n := n)⟫_[ℝ]
        + α^2 * ⟪ones (n := n), ones (n := n)⟫_[ℝ] := by
  unfold shifted
  simp [RCLike.wInner, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right];
  simp [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, pow_two];
  simp [mul_comm, mul_assoc, sub_eq_add_neg]
  ring

lemma inner_shifted_le_expr
    {n d w : ℕ} {α : ℝ} {x y : BitVec n}
    (hα : 0 ≤ α)
    (hxy_dist : d ≤ hdist x y)
    (hx_wt : wt x ≤ w)
    (hy_wt : wt y ≤ w) :
    ⟪shifted α x, shifted α y⟫_[ℝ]
      ≤ ((n : ℝ) - 2 * (d : ℝ))
        + α^2 * (n : ℝ)
        + 2 * α * (2 * (w : ℝ) - (n : ℝ)) := by
  have h_inner_bound : (RCLike.wInner 1 (CodingTheory.Johnson.shifted α x) (CodingTheory.Johnson.shifted α y)) = (n - 2 * (hdist x y : ℝ)) - α * (n - 2 * (wt x : ℝ)) - α * (n - 2 * (wt y : ℝ)) + α^2 * n := by
    convert inner_shifted_expand α x y using 1;
    erw [ inner_pmOne_pmOne, inner_pmOne_ones, inner_ones_ones ] ; norm_num ; ring;
    erw [ inner_pmOne_ones ] ; norm_num ; ring ; aesop;
  nlinarith [ ( by norm_cast : ( d : ℝ ) ≤ CodingTheory.Johnson.hdist x y ), ( by norm_cast : ( CodingTheory.Johnson.wt x : ℝ ) ≤ w ), ( by norm_cast : ( CodingTheory.Johnson.wt y : ℝ ) ≤ w ) ]

lemma alpha_nonneg (n d : ℕ) : 0 ≤ alpha n d := by
  exact Real.sqrt_nonneg _

lemma alpha_sq
    {n d : ℕ} (hn : 0 < n) (hd : 2 * d ≤ n) :
    (alpha n d)^2 = (((n : ℝ) - 2 * (d : ℝ)) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hnum_nonneg : 0 ≤ ((n : ℝ) - 2 * (d : ℝ)) := by
    have hcast : (2 : ℝ) * (d : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hd
    linarith
  have harg_nonneg : 0 ≤ (((n : ℝ) - 2 * (d : ℝ)) / (n : ℝ)) := by
    exact div_nonneg hnum_nonneg (le_of_lt hnR)
  have hs :
      (Real.sqrt ((((n : ℝ) - 2 * (d : ℝ)) / (n : ℝ))))^2
        = (((n : ℝ) - 2 * (d : ℝ)) / (n : ℝ)) := by
    exact Real.sq_sqrt harg_nonneg
  simpa [alpha] using hs

lemma alpha_lt_one_of_hd1
    {n d : ℕ} (hn : 0 < n) (hd1 : 1 ≤ d) (hd : 2 * d ≤ n) :
    alpha n d < 1 := by
  have h_alpha_lt_one : (n - 2 * d : ℝ) / n < 1 := by
    have h_frac_lt_one : (n - 2 * d : ℝ) < n := by
      norm_num [hd1];
      exact hd1;
    rwa [ div_lt_one ( by positivity ) ];
  have h_sqrt_lt_one : Real.sqrt ((n - 2 * d : ℝ) / n) < Real.sqrt 1 := by
    apply Real.sqrt_lt_sqrt; exact div_nonneg (sub_nonneg_of_le (by norm_cast)) (Nat.cast_nonneg n); exact h_alpha_lt_one.trans_le (by norm_num);
  convert h_sqrt_lt_one using 1
  simp [Real.sqrt_one]

lemma johnson_arith
    {n d w : ℕ}
    (hn : 0 < n)
    (hd : 2 * d ≤ n)
    (hw : (w : ℝ) ≤ J2 n d) :
    ((n : ℝ) - 2 * (d : ℝ))
      + (alpha n d)^2 * (n : ℝ)
      + 2 * (alpha n d) * (2 * (w : ℝ) - (n : ℝ))
      ≤ 0 := by
  have h_subst : 2 * (w : ℝ) ≤ n - Real.sqrt (n * (n - 2 * d)) := by
    unfold CodingTheory.Johnson.J2 at hw; linarith;
  rw [ show ( CodingTheory.Johnson.alpha n d ) = Real.sqrt ( ( n - 2 * d ) / n ) by rfl, Real.sq_sqrt <| div_nonneg ( sub_nonneg.2 <| mod_cast hd ) <| Nat.cast_nonneg _ ];
  rw [ Real.sqrt_div ( by nlinarith [ ( by norm_cast : ( 2 * d :ℝ ) ≤ n ) ] ) ] at *;
  rw [ Real.sqrt_mul <| by positivity ] at h_subst;
  field_simp;
  nlinarith [ show 0 ≤ Real.sqrt n * Real.sqrt ( n - 2 * d ) by positivity, show 0 ≤ Real.sqrt n by positivity, show 0 ≤ Real.sqrt ( n - 2 * d ) by positivity, Real.mul_self_sqrt ( show ( n : ℝ ) ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( n - 2 * d : ℝ ) ≥ 0 by exact sub_nonneg_of_le ( mod_cast hd ) ) ]




/-
The inner product of the projections of two vectors x and y onto the orthogonal complement of u is non-positive, provided x and y have non-positive inner products with each other and with u.
-/
lemma inner_proj_le_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u x y : V) (hu : ‖u‖ = 1) (hxu : inner ℝ x u ≤ 0) (hyu : inner ℝ y u ≤ 0) (hxy : inner ℝ x y ≤ 0) :
    inner ℝ (x - (inner ℝ x u) • u) (y - (inner ℝ y u) • u) ≤ 0 := by
      simp_all +decide [ inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right ];
      simp_all +decide [ real_inner_comm, inner_self_eq_norm_sq_to_K ] ; nlinarith;

/-
The squared norm of the projection of x onto the orthogonal complement of a unit vector u is ‖x‖² - ⟨x, u⟩².
-/
lemma proj_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u x : V) (hu : ‖u‖ = 1) :
    ‖x - (inner ℝ x u) • u‖^2 = ‖x‖^2 - (inner ℝ x u)^2 := by
      rw [ @norm_sub_sq ℝ ] ; simp +decide [ hu, inner_smul_right ] ; ring;
      simp +decide [ hu, norm_smul, mul_pow ] ; ring;

/-
The projection of a unit vector x onto the orthogonal complement of a unit vector u is non-zero, unless x is u or -u.
-/
lemma proj_nonzero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u x : V) (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) (hxu : inner ℝ x u ≤ 0) (hne : x ≠ -u) (hne' : x ≠ u) :
    x - (inner ℝ x u) • u ≠ 0 := by
      contrapose! hne';
      -- If $x - \alpha u = 0$, then $x = \alpha u$.
      obtain ⟨α, hα⟩ : ∃ α : ℝ, x = α • u := by
        exact ⟨ _, sub_eq_zero.mp hne' ⟩;
      simp_all +decide [ norm_smul, inner_smul_left ];
      rw [ abs_eq ] at hx <;> aesop

/-
The projection onto the orthogonal complement of u is injective on a set of unit vectors that all have non-positive inner product with u.
-/
lemma proj_inj_on {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (S : Set V) (hu : ‖u‖ = 1)
    (hS_norm : ∀ x ∈ S, ‖x‖ = 1) (hS_inner : ∀ x ∈ S, inner ℝ x u ≤ 0) :
    Set.InjOn (fun x => x - (inner ℝ x u) • u) S := by
      intro x hx y hy hxy;
      set c := inner ℝ x u - inner ℝ y u
      have hxy_eq : x - y = c • u := by
        simp +zetaDelta at *;
        rw [ sub_smul, ← sub_eq_zero ] ; rw [ ← sub_eq_zero_of_eq hxy ] ; abel_nf;
      have h_norm_sq : ‖x - y‖^2 = 2 - 2 * ⟪x, y⟫ := by
        rw [ @norm_sub_sq ℝ ] ; norm_num [ hS_norm x hx, hS_norm y hy ] ; ring;
      have h_norm_sq_c : ‖x - y‖^2 = c^2 := by
        rw [ hxy_eq, norm_smul, hu, Real.norm_eq_abs, abs_eq_max_neg, max_def ] ; split_ifs <;> ring;
      have h_norm_sq_x : ‖x‖^2 = ‖y + c • u‖^2 := by
        rw [ ← hxy_eq, add_sub_cancel ];
      have h_norm_sq_y : ‖y + c • u‖^2 = 1 + 2 * c * ⟪y, u⟫ + c^2 := by
        rw [ @norm_add_sq ℝ ] ; simp +decide [ *, inner_smul_right, inner_smul_left ] ; ring;
        simp +decide [ norm_smul, hu ];
      have h_c_zero_or_neg_two_beta : c = 0 ∨ c = -2 * ⟪y, u⟫ := by
        exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ h <| by nlinarith [ hS_norm x hx, hS_norm y hy ] ;
      grind


open Classical
open scoped RealInnerProductSpace

lemma rankin_reduction
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (S : Finset V) (u : V) (hu : u ∈ S) (hunit : ∀ v ∈ S, ‖v‖ = 1)
    (hpair : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → inner ℝ v w ≤ 0) :
    ∃ (S' : Finset (Submodule.span ℝ {u})ᗮ),
      S'.card = (S.filter (λ x => x ≠ u ∧ x ≠ -u)).card ∧
      (∀ v ∈ S', ‖v‖ = 1) ∧
      (∀ v ∈ S', ∀ w ∈ S', v ≠ w → inner ℝ v w ≤ 0) := by
      sorry



/-
General Rankin bound: A set of unit vectors in an n-dimensional real inner product space with pairwise non-positive inner products has size at most 2n.
-/
open Classical
open scoped RealInnerProductSpace

theorem rankin_bound_general {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Finset V) (hunit : ∀ u ∈ S, ‖u‖ = 1)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → inner ℝ u v ≤ 0) :
    S.card ≤ 2 * Module.finrank ℝ V := by
    sorry







theorem rankin_finset_bound
    {n : ℕ} (S : Finset (Euc n))
    (hunit : ∀ u ∈ S, ‖u‖ = 1)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ⟪u, v⟫_[ℝ] ≤ 0) :
    S.card ≤ 2 * n := by
  convert rankin_bound_general S _ _ ; aesop;
  · assumption;
  · norm_num [ RCLike.wInner ] at * ; aesop;

lemma shifted_ne_zero_of_alpha_lt_one
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : BitVec n) :
    shifted α x ≠ 0 := by
  intro hzero
  let i : Fin n := ⟨0, hn⟩
  have hcoord : shifted α x i = 0 := by
    have h := congrArg (fun v : Euc n => v i) hzero
    simpa using h
  by_cases hx : x i
  · have hform : shifted α x i = (-1 : ℝ) - α := by
      simp [shifted, pmOne, ones, hx]
    linarith
  · have hform : shifted α x i = (1 : ℝ) - α := by
      simp [shifted, pmOne, ones, hx]
    linarith


theorem binary_johnson_card_bound_parametric
    {n d w : ℕ}
    (hn : 0 < n)
    (C : Finset (BitVec n))
    (hpair : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hdist x y)
    (hwt : ∀ x ∈ C, wt x ≤ w)
    (α : ℝ)
    (hα : 0 ≤ α)
    (hnonzero : ∀ x ∈ C, shifted α x ≠ 0)
    (harith :
      ((n : ℝ) - 2 * (d : ℝ))
        + α^2 * (n : ℝ)
        + 2 * α * (2 * (w : ℝ) - (n : ℝ))
        ≤ 0) :
    C.card ≤ 2 * n := by
  classical
  let u : BitVec n → Euc n := fun x => shifted α x

  have hpair_u :
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ⟪u x, u y⟫_[ℝ] ≤ 0 := by
    intro x hx y hy hxy
    have hdist_xy : d ≤ hdist x y := hpair x hx y hy hxy
    have hwt_x : wt x ≤ w := hwt x hx
    have hwt_y : wt y ≤ w := hwt y hy
    have h1 :
        ⟪u x, u y⟫_[ℝ]
          ≤ ((n : ℝ) - 2 * (d : ℝ))
            + α^2 * (n : ℝ)
            + 2 * α * (2 * (w : ℝ) - (n : ℝ)) := by
      simpa [u] using
        (inner_shifted_le_expr (n := n) (d := d) (w := w) (α := α)
      (x := x) (y := y) hα hdist_xy hwt_x hwt_y)
    linarith

  let U : Finset (Euc n) := C.image (fun x => normalize (u x))

  have h_injOn :
      Set.InjOn (fun x : BitVec n => normalize (u x)) (↑C : Set (BitVec n)) := by
    intro x hx y hy; have := hnonzero x hx; have := hnonzero y hy; simp_all +decide [ normalize ] ;
    intro h_eq; specialize hpair_u x hx y hy; contrapose! hpair_u; simp_all +decide [ RCLike.wInner ] ;
    -- Since $u x = ‖u x‖ • ‖u y‖⁻¹ • u y$, we can substitute this into the inner product.
    have h_inner : ∑ i, u y i * u x i = ‖u x‖ * ‖u y‖⁻¹ * ∑ i, u y i * u y i := by
      have h_inner : u x = ‖u x‖ • ‖u y‖⁻¹ • u y := by
        rw [ ← h_eq, smul_smul, mul_inv_cancel₀ ( norm_ne_zero_iff.mpr ( hnonzero x hx ) ), one_smul ];
      conv_lhs => rw [ h_inner ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
      simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_assoc];
    rw [ h_inner ];
    refine' mul_pos ( mul_pos ( norm_pos_iff.mpr ( hnonzero x hx ) ) ( inv_pos.mpr ( norm_pos_iff.mpr ( hnonzero y hy ) ) ) ) ( lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ( Ne.symm _ ) ) ; intro H ; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_self_nonneg ] ;
    exact hnonzero y hy ( funext H )

  have hcardU : U.card = C.card := by
    unfold U
    exact Finset.card_image_of_injOn h_injOn

  have hunitU : ∀ z ∈ U, ‖z‖ = 1 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hxC, rfl⟩
    have hx0 : u x ≠ 0 := hnonzero x hxC
    simp [normalize, hx0];
    -- The norm of a scalar multiple of a vector is the absolute value of the scalar times the norm of the vector
    simp [norm_smul, hx0]

  have hpairU : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → ⟪a, b⟫_[ℝ] ≤ 0 := by
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨x, hxC, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨y, hyC, rfl⟩
    have hx0 : u x ≠ 0 := hnonzero x hxC
    have hy0 : u y ≠ 0 := hnonzero y hyC
    have hxy : x ≠ y := by
      intro hEq
      apply hab
      simp [normalize, hEq]
    have hbase : ⟪u x, u y⟫_[ℝ] ≤ 0 := hpair_u x hxC y hyC hxy
    -- Since the norms are 1 the inner product simplifies to the inner product of the original vectors
    have h_inner_simplified : ⟪normalize (u x), normalize (u y)⟫_[ℝ] = (1 / (‖u x‖ * ‖u y‖)) * ⟪u x, u y⟫_[ℝ] := by
      simp +decide [ normalize, hx0, hy0, RCLike.wInner ] ; ring;
      simp +decide only [mul_assoc, mul_left_comm, Finset.mul_sum _ _ _];
    exact h_inner_simplified.symm ▸ mul_nonpos_of_nonneg_of_nonpos ( one_div_nonneg.mpr ( mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ) hbase


  have h_rankin : U.card ≤ 2 * n := rankin_finset_bound (n := n) U hunitU hpairU
  simpa [hcardU] using h_rankin

theorem binary_johnson_card_bound
    {n d w : ℕ}
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd : 2 * d ≤ n)
    (C : Finset (BitVec n))
    (hpair : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hdist x y)
    (hwt : ∀ x ∈ C, wt x ≤ w)
    (hwJ : (w : ℝ) ≤ J2 n d) :
    C.card ≤ 2 * n := by
  let α : ℝ := alpha n d

  have hα0 : 0 ≤ α := by
    simpa [α] using alpha_nonneg n d

  have hα1 : α < 1 := by
    simpa [α] using alpha_lt_one_of_hd1 (n := n) (d := d) hn hd1 hd

  have hnonzero : ∀ x ∈ C, shifted α x ≠ 0 := by
    intro x hx
    exact shifted_ne_zero_of_alpha_lt_one (n := n) hn hα0 hα1 x

  have harith :
      ((n : ℝ) - 2 * (d : ℝ))
        + α^2 * (n : ℝ)
        + 2 * α * (2 * (w : ℝ) - (n : ℝ))
        ≤ 0 := by
    simpa [α] using johnson_arith (n := n) (d := d) (w := w) hn hd hwJ

  exact binary_johnson_card_bound_parametric
    (n := n) (d := d) (w := w)
    hn C hpair hwt α hα0 hnonzero harith

theorem binary_johnson_card_bound_of_admissible
    {n d w : ℕ}
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd : 2 * d ≤ n)
    (C : Finset (BitVec n))
    (hC : AdmissibleCode n d w C)
    (hwJ : (w : ℝ) ≤ J2 n d) :
    C.card ≤ 2 * n := by
  rcases hC with ⟨hpair, hwt⟩
  exact binary_johnson_card_bound (n := n) (d := d) (w := w)
    hn hd1 hd C hpair hwt hwJ

end Johnson

end CodingTheory

end

/-
Definition of A0(n,d,w) as the maximum size of an admissible code.
-/
open CodingTheory.Johnson

noncomputable def A0 (n d w : ℕ) : ℕ :=
  let _ : DecidablePred (AdmissibleCode n d w) := Classical.decPred _
  ((Finset.univ : Finset (CodingTheory.Johnson.BitVec n)).powerset.filter (AdmissibleCode n d w)).sup Finset.card

/-
If every admissible code has size at most K, then A0(n,d,w) is at most K.
-/
open CodingTheory.Johnson

lemma A0_le_of_forall_le
    {n d w K : ℕ}
    (h : ∀ C : Finset (CodingTheory.Johnson.BitVec n), AdmissibleCode n d w C → C.card ≤ K) :
    A0 n d w ≤ K := by
      exact Finset.sup_le fun C hC => by aesop;

/-
The binary Johnson bound (radius form): A0(n,d,w) <= 2n.
-/
open CodingTheory.Johnson

theorem binary_johnson_bound_radius
    {n d w : ℕ}
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd : 2 * d ≤ n)
    (hwJ : (w : ℝ) ≤ J2 n d) :
    A0 n d w ≤ 2 * n := by
      refine' A0_le_of_forall_le _;
      exact fun C a => binary_johnson_card_bound_of_admissible hn hd1 hd C a hwJ
