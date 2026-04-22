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
  WithLp.toLp 2 (fun i => if x i then (-1 : ℝ) else (1 : ℝ))

def ones {n : ℕ} : Euc n :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

def shifted {n : ℕ} (α : ℝ) (x : BitVec n) : Euc n :=
  pmOne x - α • ones

def normalize {n : ℕ} (u : Euc n) : Euc n :=
  (‖u‖)⁻¹ • u

@[simp] lemma ones_apply {n : ℕ} (i : Fin n) : ones (n := n) i = (1 : ℝ) := by simp [ones]

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
open scoped InnerProductSpace
open Finset
noncomputable section
open Classical in
attribute [local instance] Classical.dec
/-- Orthogonal projection onto the complement of span {u}. -/
def orthProj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (v : V) : V :=
  v - (inner ℝ u v) • u
/-
PROVIDED SOLUTION
Introduce x ∈ span {u}, get x = k•u via Submodule.mem_span_singleton. Then ⟪k•u, v - ⟪u,v⟫•u⟫ = k(⟪u,v⟫ - ⟪u,v⟫·⟪u,u⟫) = 0 since ⟪u,u⟫ = ‖u‖² = 1.
-/
lemma orthProj_mem_orthogonal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) :
    orthProj u v ∈ (Submodule.span ℝ {u})ᗮ := by
      intro x hx
      obtain ⟨k, rfl⟩ : ∃ k : ℝ, x = k • u := by
        exact Submodule.mem_span_singleton.mp hx |> Exists.imp fun k hk => hk.symm
      simp [orthProj] at *;
      simp +decide [ inner_sub_right, inner_smul_left, inner_smul_right, hu ];
      ring
/-
PROVIDED SOLUTION
If v - ⟪u,v⟫•u = 0, then v = ⟪u,v⟫•u. Taking norms: 1 = |⟪u,v⟫|·1, so |⟪u,v⟫| = 1, meaning v = u or v = -u, contradiction.
-/
lemma orthProj_ne_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hne1 : v ≠ u) (hne2 : v ≠ -u) :
    orthProj u v ≠ 0 := by
      -- Assume for contradiction that $v - ⟪u, v⟫ • u = 0$.
      by_contra h_contra
      have h_eq : v = (inner ℝ u v) • u := by
        exact eq_of_sub_eq_zero h_contra;
      -- Taking norms on both sides, we get $1 = |⟪u, v⟫|$.
      have h_norm : |(inner ℝ u v)| = 1 := by
        replace h_eq := congr_arg Norm.norm h_eq ; simp_all +decide [ norm_smul ] ;
      rcases eq_or_eq_neg_of_abs_eq h_norm with ( h | h ) <;> simp +decide [ h ] at h_eq ⊢ <;> tauto;
/-
PROVIDED SOLUTION
First show orthProj_inner: ⟪proj v, proj w⟫ = ⟪v,w⟫ - ⟪u,v⟫·⟪u,w⟫ by expanding the inner product bilinearly (unfold orthProj, use inner_sub_left/right, inner_smul_left/right, and ‖u‖=1). Then: ⟪v,w⟫ ≤ 0, and ⟪u,v⟫ = ⟪v,u⟫ ≤ 0, ⟪u,w⟫ = ⟪w,u⟫ ≤ 0 (by real_inner_comm), so ⟪u,v⟫·⟪u,w⟫ ≥ 0. Result ≤ 0 by nlinarith.
-/
lemma orthProj_inner_nonpos {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v w : V) (hu : ‖u‖ = 1)
    (hvw : inner ℝ v w ≤ 0) (hvu : inner ℝ v u ≤ 0) (hwu : inner ℝ w u ≤ 0) :
    inner ℝ (orthProj u v) (orthProj u w) ≤ 0 := by
      unfold orthProj; simp +decide [ *, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right ] ; ring_nf; (
      nlinarith [ real_inner_comm u w, real_inner_comm v u ]);

lemma normalized_orthProj_injective {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v w : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvu : inner ℝ v u ≤ 0) (hwu : inner ℝ w u ≤ 0)
    (hvw_ip : inner ℝ v w ≤ 0)
    (hv1 : v ≠ u) (hv2 : v ≠ -u) (hw1 : w ≠ u) (hw2 : w ≠ -u)
    (hvw : v ≠ w)
    (h_eq : (‖orthProj u v‖⁻¹ • orthProj u v : V) =
            (‖orthProj u w‖⁻¹ • orthProj u w : V)) :
    False := by
      -- From h_eq, we have orthProj u v = c • orthProj u w with c = ‖orthProj u v‖/‖orthProj u w‖ > 0.
      obtain ⟨c, hc⟩ : ∃ c : ℝ, 0 < c ∧ orthProj u v = c • orthProj u w := by
        refine' ⟨ ‖orthProj u v‖ / ‖orthProj u w‖, div_pos ( norm_pos_iff.mpr ( orthProj_ne_zero u v hu hv hv1 hv2 ) ) ( norm_pos_iff.mpr ( orthProj_ne_zero u w hu hw hw1 hw2 ) ), _ ⟩;
        convert congr_arg ( fun x => ‖orthProj u v‖ • x ) h_eq using 1 <;> norm_num [ div_eq_mul_inv, smul_smul ];
        rw [ mul_inv_cancel₀ ] <;> norm_num;
        exact?;
      -- Compute ⟪v,w⟫ = c(1 - ⟪u,w⟫²) + ⟪u,v⟫⟪u,w⟫.
      have h_inner : ⟪v, w⟫_ℝ = c * (1 - ⟪u, w⟫_ℝ ^ 2) + ⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ := by
        have h_sub : v - ⟪u, v⟫_ℝ • u = c • (w - ⟪u, w⟫_ℝ • u) := hc.2
        -- Substitute h_sub into the inner product expression.
        have h_inner : ⟪v, w⟫_ℝ = ⟪c • (w - ⟪u, w⟫_ℝ • u) + ⟪u, v⟫_ℝ • u, w⟫_ℝ := by
          rw [ ← h_sub, sub_add_cancel ];
        rw [ h_inner, inner_add_left, inner_smul_left, inner_sub_left, inner_smul_left ] ; ring;
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, inner_smul_left, inner_smul_right, hu, hv, hw ] ; ring
      -- Since $w \neq \pm u$, we have $|⟪u, w⟫| < 1$.
      have h_abs : |⟪u, w⟫_ℝ| < 1 := by
        have h_abs : ‖w - u‖ > 0 ∧ ‖w + u‖ > 0 := by
          exact ⟨ norm_pos_iff.mpr ( sub_ne_zero.mpr hw1 ), norm_pos_iff.mpr ( add_eq_zero_iff_eq_neg.not.mpr hw2 ) ⟩;
        have := norm_add_sq_real w u; have := norm_sub_sq_real w u; simp_all +decide [ real_inner_comm ] ;
        exact abs_lt.mpr ⟨ by nlinarith [ norm_pos_iff.mpr h_abs.1, norm_pos_iff.mpr h_abs.2 ], by nlinarith [ norm_pos_iff.mpr h_abs.1, norm_pos_iff.mpr h_abs.2 ] ⟩;
      simp_all +decide [ real_inner_comm ];
      nlinarith [ abs_lt.mp h_abs, mul_le_mul_of_nonneg_left hwu hc.1.le ]

lemma norm_normalized_orthProj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hne1 : v ≠ u) (hne2 : v ≠ -u) :
    ‖‖orthProj u v‖⁻¹ • orthProj u v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (orthProj_ne_zero u v hu hv hne1 hne2))]
lemma normalized_orthProj_inner_nonpos {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v w : V) (hu : ‖u‖ = 1)
    (hvw : inner ℝ v w ≤ 0) (hvu : inner ℝ v u ≤ 0) (hwu : inner ℝ w u ≤ 0)
    (_hv_ne : orthProj u v ≠ 0) (_hw_ne : orthProj u w ≠ 0) :
    inner ℝ (‖orthProj u v‖⁻¹ • orthProj u v)
            (‖orthProj u w‖⁻¹ • orthProj u w) ≤ 0 := by
  simp only [inner_smul_left, inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _))
    (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _))
      (orthProj_inner_nonpos u v w hu hvw hvu hwu))
lemma finrank_orthogonal_span_singleton {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (u : V) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (↥(Submodule.span ℝ {u})ᗮ) = Module.finrank ℝ V - 1 := by
  have h1 : Module.finrank ℝ (↥(ℝ ∙ u)) = 1 := by
    apply finrank_span_singleton; intro h; simp [h] at hu
  have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)
  omega
lemma card_filter_add_two {V : Type*} [AddGroup V]
    (S : Finset V) (u : V) (_hu : u ∈ S) :
    S.card ≤ (S.filter (fun v => v ≠ u ∧ v ≠ -u)).card + 2 := by
  classical
  suffices (S.filter (fun v => ¬(v ≠ u ∧ v ≠ -u))).card ≤ 2 by
    have := Finset.card_filter_add_card_filter_not (s := S) (fun v => v ≠ u ∧ v ≠ -u)
    omega
  have hsub : S.filter (fun v => ¬(v ≠ u ∧ v ≠ -u)) ⊆ {u, -u} := by
    intro v hv
    simp only [Finset.mem_filter, not_and_or, not_ne_iff] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (Finset.card_insert_le u {-u}) (by simp))
private def mkProj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (hu : ‖u‖ = 1) (v : V) : (↑(Submodule.span ℝ {u})ᗮ) :=
  ⟨‖orthProj u v‖⁻¹ • orthProj u v,
   Submodule.smul_mem _ _ (orthProj_mem_orthogonal u v hu)⟩
private lemma mkProj_val {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (hu : ‖u‖ = 1) (v : V) :
    ((mkProj u hu v : (↑(Submodule.span ℝ {u})ᗮ)) : V) = ‖orthProj u v‖⁻¹ • orthProj u v := rfl
/-- Rankin's bound: A set of unit vectors with pairwise non-positive inner products
    in a finite-dimensional real inner product space has at most 2·dim vectors. -/
theorem rankin_bound_general {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (S : Finset V) (hunit : ∀ u ∈ S, ‖u‖ = 1)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → inner ℝ u v ≤ 0) :
    S.card ≤ 2 * Module.finrank ℝ V := by
  induction' hd : Module.finrank ℝ V with d ih generalizing V S
  -- Base case: dim = 0
  · rw [Module.finrank_zero_iff] at hd
    suffices S.card = 0 by omega
    rw [Finset.card_eq_zero]
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
    have h0 : x = 0 := Subsingleton.elim x 0
    rw [h0] at hx; have := hunit 0 hx; norm_num at this
  -- Inductive step: dim = d + 1
  · by_cases hne : S.Nonempty
    · obtain ⟨u, hu_mem⟩ := hne
      have hu_norm : ‖u‖ = 1 := hunit u hu_mem
      -- Define the filtered set T and its image T' under the normalized projection
      let T := S.filter (fun v => v ≠ u ∧ v ≠ -u)
      let f := mkProj u hu_norm
      let T' := T.image f
      -- Step 1: S.card ≤ T.card + 2
      have hcard_ST : S.card ≤ T.card + 2 := card_filter_add_two S u hu_mem
      -- Step 2: T'.card = T.card (injectivity of f on T)
      have hcard_TT' : T'.card = T.card := by
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        by_contra h_ne
        have ha' := (Finset.mem_coe.mp ha)
        have hb' := (Finset.mem_coe.mp hb)
        rw [Finset.mem_filter] at ha' hb'
        have h_eq_val : (‖orthProj u a‖⁻¹ • orthProj u a : V) =
                        ‖orthProj u b‖⁻¹ • orthProj u b :=
          congr_arg Subtype.val hab
        exact normalized_orthProj_injective u a b hu_norm
          (hunit a ha'.1) (hunit b hb'.1)
          (hpair a ha'.1 u hu_mem ha'.2.1)
          (hpair b hb'.1 u hu_mem hb'.2.1)
          (hpair a ha'.1 b hb'.1 h_ne)
          ha'.2.1 ha'.2.2 hb'.2.1 hb'.2.2 h_ne h_eq_val
      -- Step 3: finrank of orthogonal complement
      have h_finrank : Module.finrank ℝ (↑(Submodule.span ℝ {u})ᗮ) = d := by
        have := finrank_orthogonal_span_singleton u hu_norm; omega
      -- Step 4: T' consists of unit vectors
      have hT'_unit : ∀ v ∈ T', ‖(v : V)‖ = 1 := by
        intro v hv
        obtain ⟨w, hw, hwf⟩ := Finset.mem_image.mp hv
        have hw' := Finset.mem_filter.mp hw
        rw [← hwf, mkProj_val]
        exact norm_normalized_orthProj u w hu_norm (hunit w hw'.1) hw'.2.1 hw'.2.2
      -- Step 5: T' has pairwise non-positive inner products
      have hT'_pair : ∀ v ∈ T', ∀ w ∈ T', v ≠ w → inner ℝ (v : V) (w : V) ≤ 0 := by
        intro v hv w hw hvw
        obtain ⟨a, ha, haf⟩ := Finset.mem_image.mp hv
        obtain ⟨b, hb, hbf⟩ := Finset.mem_image.mp hw
        have ha' := Finset.mem_filter.mp ha
        have hb' := Finset.mem_filter.mp hb
        rw [← haf, ← hbf]
        simp only [f, mkProj_val]
        apply normalized_orthProj_inner_nonpos u a b hu_norm
        · exact hpair a ha'.1 b hb'.1 (fun heq => hvw (by rw [← haf, ← hbf, heq]))
        · exact hpair a ha'.1 u hu_mem ha'.2.1
        · exact hpair b hb'.1 u hu_mem hb'.2.1
        · exact orthProj_ne_zero u a hu_norm (hunit a ha'.1) ha'.2.1 ha'.2.2
        · exact orthProj_ne_zero u b hu_norm (hunit b hb'.1) hb'.2.1 hb'.2.2
      -- Step 6: Apply IH to get T'.card ≤ 2 * d
      have hT'_bound : T'.card ≤ 2 * d := h_finrank ▸ ih T' hT'_unit hT'_pair h_finrank
      -- Combine
      linarith
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]; simp
end

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
    exact hnonzero y hy ( PiLp.ext H )

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
