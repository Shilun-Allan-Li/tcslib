import Mathlib

namespace ZkFourier
end ZkFourier

open Finset Complex

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace ZkFourier
def ZkVec (k n : ℕ) := Fin n → ZMod k
end ZkFourier

namespace ZkFourier
noncomputable def rootOfUnity (k : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * I / (k : ℂ))
end ZkFourier

namespace ZkFourier
noncomputable def toOmega {k : ℕ} [NeZero k] (a : ZMod k) : ℂ :=
  rootOfUnity k ^ a.val
end ZkFourier

namespace ZkFourier
lemma isPrimitiveRoot_rootOfUnity {k : ℕ} [NeZero k] :
    IsPrimitiveRoot (rootOfUnity k) k :=
  Complex.isPrimitiveRoot_exp k (NeZero.ne k)
end ZkFourier

namespace ZkFourier
lemma rootOfUnity_pow_k {k : ℕ} [NeZero k] :
    rootOfUnity k ^ k = 1 :=
  isPrimitiveRoot_rootOfUnity.pow_eq_one
end ZkFourier

namespace ZkFourier
lemma toOmega_add {k : ℕ} [NeZero k] (a b : ZMod k) :
    toOmega (a + b) = toOmega a * toOmega b := by
      unfold toOmega; simp +decide [ ← pow_add ] ;
      rw [ ← Nat.mod_add_div ( a.val + b.val ) k, pow_add, pow_mul ] ; norm_num [ rootOfUnity_pow_k ];
      rw [ ZMod.val_add ]
end ZkFourier

namespace ZkFourier
lemma toOmega_neg {k : ℕ} [NeZero k] (a : ZMod k) :
    toOmega (-a) = starRingEnd ℂ (toOmega a) := by
      by_cases ha : a.val = 0 <;> simp_all +decide;
      have h_neg : (-a).val = k - a.val := by
        convert ZMod.neg_val' a using 1;
        rw [ Nat.mod_eq_of_lt ( Nat.sub_lt ( NeZero.pos k ) ( Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using ha ) ) ) ];
      unfold toOmega rootOfUnity;
      rw [ h_neg, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul ];
      rw [ Nat.cast_sub ( show a.val ≤ k from a.val_lt.le ) ] ; simp +decide [ Complex.ext_iff, Complex.exp_re, Complex.exp_im];
      norm_num [ sub_mul, mul_div_cancel₀, NeZero.ne ];
      erw [ ZMod.cast_eq_val ] ; norm_cast ; aesop
end ZkFourier

namespace ZkFourier
def ZkFun (k n : ℕ) := ZkVec k n → ℂ
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def expectation (f : ZkFun k n) : ℂ :=
  (∑ x : ZkVec k n, f x) / (k : ℂ) ^ n
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def inner_product (f g : ZkFun k n) : ℂ :=
  expectation (fun x => f x * starRingEnd ℂ (g x))
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
def zkDot (s x : ZkVec k n) : ZMod k := ∑ i : Fin n, s i * x i
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def char_s (s : ZkVec k n) : ZkFun k n :=
  fun x => toOmega (zkDot s x)
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
lemma zkDot_add_right (s x y : ZkVec k n) :
    zkDot s (x + y) = zkDot s x + zkDot s y := by
      unfold zkDot;
      simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun _ _ => mul_add _ _ _
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def fourier_coeff (f : ZkFun k n) (s : ZkVec k n) : ℂ :=
  inner_product f (char_s s)
end ZkFourier

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open Finset Complex ZkFourier

set_option linter.unusedSectionVars false

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
def is_linear (f : ZkVec k n → ZMod k) : Prop :=
  ∀ x y, f (x + y) = f x + f y
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def lift_omega (f : ZkVec k n → ZMod k) : ZkFun k n :=
  fun x => toOmega (f x)
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def zk_dist (f g : ZkVec k n → ZMod k) : ℝ :=
  (∑ x : ZkVec k n, if f x = g x then (0 : ℝ) else 1) / (k : ℝ) ^ n
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def linear_character (s : ZkVec k n) :
    ZkVec k n → ZMod k :=
  fun x => zkDot s x
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
def normalized
    (f : ZkVec k n → ZMod k) : Prop :=
  f 0 = 0
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
def epsilon_far_from_linear_normalized
    (f : ZkVec k n → ZMod k)
    (ε : ℝ) : Prop :=
  normalized f ∧
  0 ≤ ε ∧ ε ≤ 1 ∧
  ∀ g : ZkVec k n → ZMod k,
    is_linear g →
    zk_dist f g ≥ ε
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
lemma re_toOmega_le_re_rootOfUnity {k : ℕ} [NeZero k] (hk : 2 ≤ k) (a : ZMod k) (ha : a ≠ 0) :
    (toOmega a).re ≤ Real.cos (2 * Real.pi / k) := by
  -- Since a ≠ 0 in ℤ_k, we have 1 ≤ a.val ≤ k − 1.
  have h_a_val : 1 ≤ a.val ∧ a.val ≤ k - 1 := by
    exact ⟨ Nat.pos_of_ne_zero ( by simpa [ ZMod.val_eq_zero ] using ha ), Nat.le_pred_of_lt ( ZMod.val_lt a ) ⟩;
  -- The angle θ = 2πa/k satisfies 2π/k ≤ θ ≤ 2π − 2π/k.
  have h_angle : 2 * Real.pi / k ≤ 2 * Real.pi * a.val / k ∧ 2 * Real.pi * a.val / k ≤ 2 * Real.pi - 2 * Real.pi / k := by
    field_simp;
    exact ⟨ mod_cast h_a_val.1, le_tsub_of_add_le_right <| mod_cast h_a_val.2.trans_lt <| Nat.pred_lt <| ne_bot_of_gt hk ⟩;
  -- cos(θ) ≤ cos(2π/k) because cos is decreasing on [0, π] and
  -- increasing on [π, 2π] (using the identity cos(2π − θ) = cos(θ)).
  have h_cos_decreasing : Real.cos (2 * Real.pi * a.val / k) ≤ Real.cos (2 * Real.pi / k) := by
    by_cases h_case : 2 * Real.pi * a.val / k ≤ Real.pi;
    · exact Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith ) h_angle.1;
    · rw [ ← Real.cos_two_pi_sub ] ; exact Real.cos_le_cos_of_nonneg_of_le_pi ( by nlinarith [ Real.pi_pos, show ( k : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( k : ℝ ) ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( k : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( k : ℝ ) ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( k : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( k : ℝ ) ≠ 0 ) ] ) ;
  -- Finally, Re(ω_k^a) = cos(2πa/k) ≤ cos(2π/k).
  convert h_cos_decreasing using 1 ; unfold toOmega ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.cos ] ; ring_nf;
  unfold rootOfUnity; norm_num [ ← Complex.exp_nat_mul, Complex.exp_re ] ; ring_nf;
  norm_num [ ZMod.cast, ZMod.val ];
  rcases k with ( _ | _ | k ) <;> norm_num at *
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
lemma re_fourier_coeff_upper_bound
    (hk : 2 ≤ k)
    (f : ZkVec k n → ZMod k)
    (s : ZkVec k n) :
    (fourier_coeff (lift_omega f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) *
        zk_dist f (linear_character s) := by
  unfold fourier_coeff zk_dist; norm_num [ Finset.sum_ite ] ; ring_nf;
  norm_num [ inner_product, lift_omega, char_s ];
  -- Pointwise bound: on each x, the real part of ω_k^{f(x)} · conj(ω_k^{s·x})
  -- is ≤ 1 − (1 − cos(2π/k)) · 𝟙[f(x) ≠ s·x].
  have h_bound : ∀ x : ZkVec k n, (toOmega (f x) * (starRingEnd ℂ) (toOmega (zkDot s x))).re ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * (if f x = linear_character s x then 0 else 1) := by
    intro x
    by_cases hfx : f x = linear_character s x;
    · -- Agreement case: the product is |ω_k^{s·x}|² = 1.
      simp_all +decide [ linear_character ];
      unfold toOmega ; ring_nf;
      norm_num [ ← Complex.normSq_add_mul_I, Complex.normSq_eq_norm_sq, Complex.norm_exp ];
      unfold rootOfUnity; norm_num [ Complex.norm_exp ] ;
    · -- Disagreement case: ω_k^{f(x) − s·x} has Re ≤ cos(2π/k).
      have h_ineq : (toOmega (f x - zkDot s x)).re ≤ Real.cos (2 * Real.pi / k) := by
        apply re_toOmega_le_re_rootOfUnity hk;
        exact sub_ne_zero_of_ne hfx;
      -- Rewrite ω_k^{f(x) − s·x} = ω_k^{f(x)} · conj(ω_k^{s·x}).
      have h_ineq : toOmega (f x - zkDot s x) = toOmega (f x) * (starRingEnd ℂ) (toOmega (zkDot s x)) := by
        have h_ineq : toOmega (f x - zkDot s x) = toOmega (f x) * toOmega (-zkDot s x) := by
          convert toOmega_add ( f x ) ( -zkDot s x ) using 1 ; ring_nf;
        rw [ h_ineq, ← toOmega_neg ];
      aesop;
  -- Average the pointwise bound over all x ∈ ℤ_k^n.
  convert div_le_div_of_nonneg_right ( Finset.sum_le_sum fun x _ => h_bound x ) ( by positivity : ( 0 : ℝ ) ≤ k ^ n ) using 1 <;> norm_num [ Finset.sum_ite ] ; ring_nf;
  any_goals exact Finset.univ;
  · unfold expectation; norm_num [ Complex.ext_iff ] ; ring_nf;
    norm_num [ Complex.ext_iff, Finset.sum_mul _ _ _ ];
    norm_cast ; norm_num [ mul_pow ];
  · rw [ show ( #univ : ℕ ) = k ^ n from ?_ ] ; ring_nf;
    · norm_num [ add_comm, NeZero.ne ];
    · simp +decide [ Finset.card_univ, ZkVec ]
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
lemma re_epsilon_far_bounds_fourier
    (hk : 2 ≤ k)
    (f : ZkVec k n → ZMod k)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (s : ZkVec k n) :
    (fourier_coeff (lift_omega f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * ε := by
  -- Apply the pointwise bound, then use ε ≤ dist(f, linear_character s).
  refine' le_trans ( re_fourier_coeff_upper_bound hk f s ) _;
  gcongr;
  -- The constant 1 − cos(2π/k) is nonneg (since cos(2π/k) ≤ 1).
  · nlinarith [ Real.cos_sq' ( 2 * Real.pi / k ) ];
  -- dist(f, linear_character s) ≥ ε because linear_character s is linear.
  · exact hfar.2.2.2 _ ( show is_linear ( linear_character s ) from fun x y => by simp +decide [ linear_character, zkDot_add_right ] )
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def lift_omega_j (j : ZMod k) (f : ZkVec k n → ZMod k) :
    ZkFun k n :=
  fun x => toOmega (j * f x)
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
lemma unit_mul_epsilon_far
    (f : ZkVec k n → ZMod k)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (j : (ZMod k)ˣ) :
    epsilon_far_from_linear_normalized (fun x => (j : ZMod k) * f x) ε := by
  obtain ⟨hf₁, hf₂, hf₃, hf₄⟩ := hfar;
  refine' ⟨ _, hf₂, hf₃, fun g hg => _ ⟩;
  -- Normalization: j · f(0) = j · 0 = 0.
  · exact mul_eq_zero_of_right _ hf₁;
  -- Distance preservation: dist(j·f, g) = dist(f, j⁻¹·g).
  · convert hf₄ ( fun x => j⁻¹ * g x ) _ using 1;
    · unfold zk_dist;
      congr! 2;
      split_ifs <;> simp_all +decide [ mul_comm ];
      · exact ‹¬f _ = g _ * ↑j⁻¹› ( by rw [ ← ‹↑j * f _ = g _›, mul_right_comm, Units.mul_inv, one_mul ] );
      · simp_all +decide [ mul_left_comm ( j : ZMod k ), Units.mul_inv ];
    -- j⁻¹ · g is linear if g is linear.
    · intro x y; simp +decide [ hg x y, mul_add ] ;
end ZkBLR

namespace ZkBLR
variable {k : ℕ} [NeZero k] {n : ℕ}
lemma re_fourier_coeff_lift_omega_j_unit_bound
    (hk : 2 ≤ k)
    (f : ZkVec k n → ZMod k)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear_normalized f ε)
    (j : (ZMod k)ˣ)
    (s : ZkVec k n) :
    (fourier_coeff (lift_omega_j (↑j) f) s).re
      ≤ 1 - (1 - Real.cos (2 * Real.pi / k)) * ε := by
  -- Set g(x) = j·f(x). By unit_mul_epsilon_far, g is ε-far from linear.
  set g : ZkVec k n → ZMod k := fun x => (j : ZMod k) * f x;
  have hg : epsilon_far_from_linear_normalized g ε := unit_mul_epsilon_far f ε hfar j;
  convert re_epsilon_far_bounds_fourier hk g ε hg s using 1
end ZkBLR
