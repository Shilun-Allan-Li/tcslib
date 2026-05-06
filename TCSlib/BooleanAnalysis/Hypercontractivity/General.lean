import TCSlib.BooleanAnalysis.Hypercontractivity.OneBit

open BooleanAnalysis OneBit Bonami SimpleHypercontractivity Real
set_option maxHeartbeats 800000
namespace GeneralHypercontractivity
variable {n : ℕ}
/-! ## Noise Kernel -/

/-- The noise kernel `K_ρ(x, y) = ∏_i (1 + ρ · sign(x_i) · sign(y_i)) / 2`.
This is the transition probability from `x` to `y` under ρ-correlated noise. -/
noncomputable def noiseKernel (ρ : ℝ) {n : ℕ} (x y : BoolCube n) : ℝ :=
  ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) / 2

lemma noiseKernel_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x y : BoolCube n) : 0 ≤ noiseKernel ρ x y := by
  refine Finset.prod_nonneg fun i _ ↦ ?_
  cases x i <;> cases y i <;> norm_num [boolToSign] <;> nlinarith
/-! ## Noise Operator as Kernel Sum -/

lemma sum_fourier_kernel (ρ : ℝ) (x y : BoolCube n) :
    ∑ S : Finset (Fin n), ρ ^ S.card * chiS S x * chiS S y =
    ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) := by
  have h_prod_sum : ∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) =
      ∑ S : Finset (Fin n), ∏ i ∈ S, (ρ * boolToSign (x i) * boolToSign (y i)) := by
    simp +decide [add_comm, Finset.prod_add]
  rw [h_prod_sum, Finset.sum_congr rfl]
  intros; simp_all +decide [Finset.prod_mul_distrib, chiS]

/-- The noise operator equals a kernel sum: `T_ρ g(x) = ∑_y K_ρ(x,y) · g(y)`. -/
lemma noiseOp_eq_kernel_sum (ρ : ℝ) (g : BooleanFunc n) (x : BoolCube n) :
    noiseOp ρ g x = ∑ y : BoolCube n, noiseKernel ρ x y * g y := by
  unfold noiseOp noiseKernel BooleanAnalysis.fourierCoeff BooleanAnalysis.innerProduct
  simp +decide [BooleanAnalysis.expect]
  unfold uniformWeight
  simp +decide [div_eq_inv_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm, Finset.sum_congr rfl]; intros; ring_nf
  rw [← sum_fourier_kernel]
  simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum]

/-! ## Inner Product as Kernel-Weighted Sum -/

/-- `⟨f, T_ρ g⟩ = (1/2^n) ∑_{x,y} K_ρ(x,y) · f(x) · g(y)`. -/
lemma innerProduct_noiseOp_eq_weighted_sum (ρ : ℝ) (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) =
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * f x * g y := by
  unfold innerProduct
  simp +decide [mul_assoc, Finset.mul_sum, expect]
  rw [Finset.sum_congr rfl fun _ _ => ?_]
  rw [noiseOp_eq_kernel_sum]
  simp +decide [mul_comm, mul_left_comm, Finset.mul_sum]

/-! ## Correlated Monotonicity -/

/-- If `h(x,y) ≤ h'(x,y)` pointwise and `0 ≤ ρ ≤ 1`, then the kernel-weighted
expectation of `h` is at most that of `h'`. -/
lemma corrExpect_mono {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {h h' : BoolCube n → BoolCube n → ℝ} (hle : ∀ x y, h x y ≤ h' x y) :
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * h x y ≤
    uniformWeight n * ∑ x : BoolCube n, ∑ y : BoolCube n,
      noiseKernel ρ x y * h' x y := by
  apply_rules [mul_le_mul_of_nonneg_left, Finset.sum_le_sum]
  · exact fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (hle x y) (noiseKernel_nonneg hρ0 hρ1 x y)
  · exact pow_nonneg (by norm_num) _

/-! ## Noise Kernel Factorization -/

/-- The noise kernel on `BoolCube (n+1)` factors along the last coordinate. -/
lemma noiseKernel_snoc (ρ : ℝ) (x' y' : BoolCube n) (b b' : Bool) :
    noiseKernel ρ (Fin.snoc x' b) (Fin.snoc y' b') =
    noiseKernel ρ x' y' * ((1 + ρ * boolToSign b * boolToSign b') / 2) := by
  unfold noiseKernel; simp +decide [Fin.prod_univ_castSucc]; ring

/-! ## Expectation Decomposition (Fubini for BoolCube) -/

lemma expect_succ_eq_iterated (h : BooleanFunc (n + 1)) :
    expect h = expect (fun x' =>
      (1/2 : ℝ) * (h (Fin.snoc x' false) + h (Fin.snoc x' true))) := by
  unfold expect
  rw [sum_boolCube_succ]
  norm_num [Finset.mul_sum, mul_add, mul_assoc, mul_left_comm,
            Finset.sum_add_distrib, uniformWeight_succ]
  ring_nf

/-! ## Norm Collapse (Fubini) -/

lemma norm_collapse_rpow (p : ℝ) (hp : 0 < p) (f : BooleanFunc (n + 1)) :
    expect (fun x => |f x| ^ p) =
    expect (fun x' => (1/2 : ℝ) *
      (|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p)) := by
  convert expect_succ_eq_iterated _ using 1

/-! ## Decomposition of Weighted Sum at Dimension n+1 -/

/--
The kernel-weighted bilinear sum at dimension `n+1` decomposes by factoring the
kernel along the last coordinate.
-/
lemma weighted_sum_succ_decomp (ρ : ℝ) (F : BoolCube (n + 1) → BoolCube (n + 1) → ℝ) :
    uniformWeight (n + 1) * ∑ x : BoolCube (n + 1), ∑ y : BoolCube (n + 1),
      noiseKernel ρ x y * F x y =
    uniformWeight n * ∑ x' : BoolCube n, ∑ y' : BoolCube n,
      noiseKernel ρ x' y' *
      ((1/2 : ℝ) * ∑ b : Bool, ∑ b' : Bool,
        ((1 + ρ * boolToSign b * boolToSign b') / 2) *
        F (Fin.snoc x' b) (Fin.snoc y' b')) := by
  convert congr_arg _ ( sum_boolCube_succ fun y => ∑ x, noiseKernel ρ y x * F y x ) using 1 ; norm_num ; ring_nf!;
  rw [ add_comm 1, uniformWeight_succ ] ; simp +decide [ Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm,
    mul_add, Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_add, Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_add] ; ring_nf;
  simp +decide only [← Finset.sum_add_distrib] ; ring_nf;
  refine' Finset.sum_congr rfl fun x _ => _ ; rw [ sum_boolCube_succ ] ; ring_nf;
  rw [ ← Finset.sum_add_distrib ] ; congr ; ext y ; rw [ noiseKernel_snoc, noiseKernel_snoc ] ; ring_nf;
  rw [ noiseKernel_snoc, noiseKernel_snoc ] ; norm_num [ boolToSign ] ; ring;

/-! ## One-Bit Correlated Expectation as Inner Product -/

/--
For fixed `x'` and `y'`, the one-bit kernel-weighted sum of the slices of `f` and `g`
equals the one-bit inner product with noise operator.
-/
lemma one_bit_slice_eq_innerProduct (ρ : ℝ) (f g : BooleanFunc (n + 1))
    (x' y' : BoolCube n) :
    (1/2 : ℝ) * ∑ b : Bool, ∑ b' : Bool,
      ((1 + ρ * boolToSign b * boolToSign b') / 2) *
      f (Fin.snoc x' b) * g (Fin.snoc y' b') =
    innerProduct (fun t : BoolCube 1 => f (Fin.snoc x' (t 0)))
                 (noiseOp ρ (fun t : BoolCube 1 => g (Fin.snoc y' (t 0)))) := by
  unfold BooleanAnalysis.noiseOp;
  unfold BooleanAnalysis.innerProduct BooleanAnalysis.fourierCoeff
  simp;
  rw [ show ( Finset.univ : Finset ( Finset ( Fin 1 ) ) ) = { ∅, { 0 } } by decide ] ; norm_num ; ring_nf;
  unfold BooleanAnalysis.expect; norm_num [ Finset.sum_range_succ, Finset.sum_range_zero, BooleanAnalysis.innerProduct ] ; ring_nf;
  unfold BooleanAnalysis.expect; norm_num [ Finset.sum_range_succ, Finset.sum_range_zero, BooleanAnalysis.uniformWeight ] ; ring_nf;
  rw [ show ( Finset.univ : Finset ( BoolCube 1 ) ) = { fun _ => false, fun _ => true } by decide ] ; norm_num ; ring_nf;
  rw [ Finset.sum_pair, Finset.sum_pair ] <;> norm_num [ boolToSign ] ; ring_nf;
  · grind +splitImp;
  · exact fun h => by have := congr_fun h 0; simp +decide at this;
  · exact fun h => by have := congr_fun h 0; simp +decide at this;

/-! ## One-bit Lp norm of slices -/
/-
The one-bit `L^p` norm of the slice `t ↦ f(snoc x' (t 0))`.
-/
lemma one_bit_norm_slice (p : ℝ) (hp : 0 < p) (f : BooleanFunc (n + 1)) (x' : BoolCube n) :
    (expect (fun t : BoolCube 1 => |f (Fin.snoc x' (t 0))| ^ p)) ^ (1/p) =
    ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1/p) := by
  unfold expect;
  unfold uniformWeight; norm_num [ Finset.card_univ ] ; ring_nf;
  rw [ show ( Finset.univ : Finset ( Fin 1 → Bool ) ) = { fun _ => Bool.false, fun _ => Bool.true } by decide, Finset.sum_pair ] <;> norm_num ; ring_nf;
  decide +revert

/-! ## Norm Collapse (clean form) -/
/-
The iterated norm collapses: `E_{x'}[F(x')^p] = E_x[|f(x)|^p]` where
`F(x') = (E_t[|f(x',t)|^p])^{1/p}`.
-/
lemma norm_collapse_clean (p : ℝ) (hp : 1 ≤ p) (f : BooleanFunc (n + 1)) :
    expect (fun x' =>
      ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ) =
    expect (fun x => |f x| ^ p) := by
  convert norm_collapse_rpow p ( by linarith ) f |> Eq.symm using 2;
  exact funext fun x' => by ring;

/--
**Hölder inequality for Boolean functions.**
-/
lemma holder_ineq_bool {n : ℕ} (p : ℝ) (hp : 1 < p) (f h : BooleanFunc n) :
    innerProduct f h ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) *
    (expect (fun x => |h x| ^ (p / (p - 1)))) ^ ((p - 1) / p) := by
  unfold BooleanAnalysis.innerProduct;
  -- Apply the Hölder inequality to the sequences $f$ and $h$.
  have h_holder : (∑ x : BoolCube n, |f x| * |h x|) ≤ (∑ x : BoolCube n, |f x|^p) ^ (1 / p) * (∑ x : BoolCube n, |h x|^(p / (p - 1))) ^ ((p - 1) / p) := by
    have := @Real.inner_le_Lp_mul_Lq;
    convert this Finset.univ ( fun x => |f x| ) ( fun x => |h x| ) ( show Real.HolderConjugate p ( p / ( p - 1 ) ) from ?_ ) using 1;
    · norm_num [ div_div_eq_mul_div ];
    · exact (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl;
  unfold expect;
  convert mul_le_mul_of_nonneg_left h_holder ( show 0 ≤ uniformWeight n by exact pow_nonneg ( by norm_num ) _ ) |> le_trans ( show _ ≤ _ from ?_ ) using 1;
  · rw [ Real.mul_rpow ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity ), Real.mul_rpow ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => by positivity ) ] ; ring_nf;
    rw [ show p * p⁻¹ = 1 by rw [ mul_inv_cancel₀ ( by positivity ) ] ] ; rw [ show uniformWeight n = ( 2 : ℝ ) ⁻¹ ^ n by rfl ] ; rw [ Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring_nf;
    field_simp;
  · exact mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun _ _ => by rw [ ← abs_mul ] ; exact le_abs_self _ ) ( by exact pow_nonneg ( by norm_num ) _ )
/--
**Lp contractivity of the noise operator on one bit.**
For 0 ≤ ρ ≤ 1 and q ≥ 1:
  `‖T_ρ g‖_q ≤ ‖g‖_q`
-/
lemma noise_Lp_contraction_one_bit
    (q : ℝ) (hq1 : 1 ≤ q)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (g : BooleanFunc 1) :
    (expect (fun x => |noiseOp ρ g x| ^ q)) ^ (1 / q) ≤
    (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
  unfold noiseOp; norm_num;
  unfold expect;
  unfold uniformWeight; norm_num [ Fin.sum_univ_succ ] ;
  rw [ show ( Finset.univ : Finset ( BoolCube 1 ) ) = { fun _ => false, fun _ => true } by decide ];
  rw [ Finset.sum_pair, Finset.sum_pair ] <;> norm_num [ funext_iff, Fin.forall_fin_one ];
  rw [ show ( Finset.univ : Finset ( Finset ( Fin 1 ) ) ) = { ∅, { 0 } } by decide ] ; norm_num [ Finset.sum_pair ] ; ring_nf ; norm_num [ show q ≠ 0 by linarith ] ;
  -- By the properties of the absolute value and the fact that $q \geq 1$, we can apply Jensen's inequality.
  have h_jensen : ∀ a b : ℝ, |a + ρ * b| ^ q + |a - ρ * b| ^ q ≤ |a + b| ^ q + |a - b| ^ q := by
    intros a b
    have h_abs : |a + ρ * b| ≤ (1 + ρ) / 2 * |a + b| + (1 - ρ) / 2 * |a - b| ∧ |a - ρ * b| ≤ (1 + ρ) / 2 * |a - b| + (1 - ρ) / 2 * |a + b| := by
      constructor <;> rw [ abs_le ] <;> constructor <;> cases abs_cases ( a + b ) <;> cases abs_cases ( a - b ) <;> nlinarith;
    have h_jensen : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → ((1 + ρ) / 2 * x + (1 - ρ) / 2 * y) ^ q ≤ (1 + ρ) / 2 * x ^ q + (1 - ρ) / 2 * y ^ q := by
      have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ q) := by
        exact ( convexOn_rpow ( by linarith ) );
      exact fun x y hx hy => h_jensen.2 hx hy ( by linarith ) ( by linarith ) ( by linarith );
    refine le_trans ( add_le_add ( Real.rpow_le_rpow ( abs_nonneg _ ) h_abs.1 ( by positivity ) ) ( Real.rpow_le_rpow ( abs_nonneg _ ) h_abs.2 ( by positivity ) ) ) ?_;
    convert add_le_add ( h_jensen |a + b| |a - b| ( abs_nonneg _ ) ( abs_nonneg _ ) ) ( h_jensen |a - b| |a + b| ( abs_nonneg _ ) ( abs_nonneg _ ) ) using 1 ; ring;
  have := h_jensen ( fourierCoeff g ∅ ) ( fourierCoeff g { 0 } ) ; norm_num [ one_bit_val_false, one_bit_val_true ] at *;
  exact Real.rpow_le_rpow ( by positivity ) ( by linarith ) ( by positivity )

/-! ## Main Theorem: Two-Function Hypercontractivity by Induction -/

/-
Helper: the zero-dimensional case is trivial.
-/
lemma two_func_hyp_zero
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) (ρ : ℝ)
    (f g : BooleanFunc 0) :
    innerProduct f (noiseOp ρ g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1/p) *
    (expect (fun x => |g x| ^ q)) ^ (1/q) := by
  unfold innerProduct BooleanAnalysis.expect;
  unfold uniformWeight;
  -- By definition of noiseOp, we have noiseOp ρ g x = g x for any x.
  have h_noiseOp : ∀ x, noiseOp ρ g x = g x := by
    intro x;
    unfold noiseOp;
    rw [ show ( Finset.univ : Finset ( Finset ( Fin 0 ) ) ) = { ∅ } by decide, Finset.sum_singleton ] ; norm_num [ BooleanAnalysis.fourierCoeff, BooleanAnalysis.chiS ];
    unfold innerProduct; norm_num [ BooleanAnalysis.expect ] ;
    unfold uniformWeight; norm_num;
    exact congr_arg g ( Subsingleton.elim _ _ );
  simp_all +decide [ show ∀ x : Fin 0 → Bool, x = fun _ => Bool.true by intro x; ext i; exact Fin.elim0 i ];
  rw [ ← Real.rpow_mul ( abs_nonneg _ ), ← Real.rpow_mul ( abs_nonneg _ ), mul_inv_cancel₀ ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one, Real.rpow_one ];
  cases abs_cases ( f fun _ => true ) <;> cases abs_cases ( g fun _ => true ) <;> nlinarith

/-
Helper: the inductive step. Given the result for dimension n,
prove it for dimension n+1 using the one-bit base case.
-/
lemma two_func_hyp_succ
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (base_case : ∀ (f g : BooleanFunc 1),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ p)) ^ (1/p) *
      (expect (fun x => |g x| ^ q)) ^ (1/q))
    (ih : ∀ (f g : BooleanFunc n),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ p)) ^ (1/p) *
      (expect (fun x => |g x| ^ q)) ^ (1/q))
    (f g : BooleanFunc (n + 1)) :
    innerProduct f (noiseOp ρ g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1/p) *
    (expect (fun x => |g x| ^ q)) ^ (1/q) := by
  nontriviality;
  revert f g;
  intro f g;
  -- Apply the one-bit slice decomposition to rewrite the left-hand side.
  have h_lhs : ⟪f, noiseOp ρ g⟫_𝔹 = uniformWeight n * ∑ x' : BoolCube n, ∑ y' : BoolCube n, noiseKernel ρ x' y' * ⟪fun t : BoolCube 1 => f (Fin.snoc x' (t 0)), noiseOp ρ (fun t : BoolCube 1 => g (Fin.snoc y' (t 0)))⟫_𝔹 := by
    have h_lhs : ⟪f, noiseOp ρ g⟫_𝔹 = uniformWeight (n + 1) * ∑ x : BoolCube (n + 1), ∑ y : BoolCube (n + 1), noiseKernel ρ x y * f x * g y := by
      convert innerProduct_noiseOp_eq_weighted_sum ρ f g using 1;
    convert weighted_sum_succ_decomp ρ ( fun x y => f x * g y ) using 1;
    · simpa only [ mul_assoc ] using h_lhs;
    · congr! 3;
      exact congrArg _ ( one_bit_slice_eq_innerProduct ρ f g _ _ ▸ by ac_rfl );
  -- Apply the pointwise bound from `base_case` to each term in the sum.
  have h_pointwise : ∀ x' y' : BoolCube n, ⟪fun t : BoolCube 1 => f (Fin.snoc x' (t 0)), noiseOp ρ (fun t : BoolCube 1 => g (Fin.snoc y' (t 0)))⟫_𝔹 ≤
    ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1 / p) *
    ((|g (Fin.snoc y' false)| ^ q + |g (Fin.snoc y' true)| ^ q) / 2) ^ (1 / q) := by
      intro x' y';
      convert base_case _ _ using 1;
      unfold expect;
      unfold uniformWeight;
      erw [ show ( Finset.univ : Finset ( Fin 1 → Bool ) ) = { fun _ => Bool.false, fun _ => Bool.true } by decide ] ; simp +decide ; ring_nf;
  -- Apply the pointwise bound from `h_pointwise` to each term in the sum.
  have h_sum_bound : ⟪f, noiseOp ρ g⟫_𝔹 ≤ uniformWeight n * ∑ x' : BoolCube n, ∑ y' : BoolCube n, noiseKernel ρ x' y' *
    ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1 / p) *
    ((|g (Fin.snoc y' false)| ^ q + |g (Fin.snoc y' true)| ^ q) / 2) ^ (1 / q) := by
      rw [h_lhs];
      exact mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun x' _ => Finset.sum_le_sum fun y' _ => by simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left ( h_pointwise x' y' ) ( noiseKernel_nonneg hρ0 hρ1 x' y' ) ) ( by exact pow_nonneg ( by norm_num ) _ );
  -- Apply the induction hypothesis to bound the sum.
  have h_ind_bound : ⟪(fun x' => ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2) ^ (1 / p)), noiseOp ρ (fun y' => ((|g (Fin.snoc y' false)| ^ q + |g (Fin.snoc y' true)| ^ q) / 2) ^ (1 / q))⟫_𝔹 ≤
    (expect (fun x' => ((|f (Fin.snoc x' false)| ^ p + |f (Fin.snoc x' true)| ^ p) / 2))) ^ (1 / p) *
    (expect (fun y' => ((|g (Fin.snoc y' false)| ^ q + |g (Fin.snoc y' true)| ^ q) / 2))) ^ (1 / q) := by
      convert ih _ _ using 3 <;> norm_num [ abs_of_nonneg, Real.rpow_nonneg, add_nonneg, div_nonneg, Real.rpow_nonneg, abs_nonneg ];
      · exact congr_arg _ ( funext fun x => by rw [ ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] );
      · exact congr_arg _ ( funext fun x => by rw [ ← Real.rpow_mul ( by positivity ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ] );
  refine le_trans h_sum_bound ?_;
  convert h_ind_bound using 1;
  · rw [ innerProduct_noiseOp_eq_weighted_sum ];
  · congr! 2;
    · convert norm_collapse_clean p hp f |> Eq.symm using 1;
    · convert norm_collapse_clean q ( by linarith ) g |> Eq.symm using 1
/--
**Two-Function Hypercontractivity Induction Theorem**
A hypercontractive result on a single bit implies the same result on `n` bits
-/
theorem hypercontractivity_induction
    (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (base_case : ∀ (f g : BooleanFunc 1),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ p)) ^ (1/p) *
      (expect (fun x => |g x| ^ q)) ^ (1/q))
    {n : ℕ} (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1/p) *
    (expect (fun x => |g x| ^ q)) ^ (1/q) := by
  induction n with
  | zero => exact two_func_hyp_zero p q hp hq ρ f g
  | succ n ih =>
    exact two_func_hyp_succ p q hp hq ρ hρ0 hρ1 base_case
      (fun f' g' => ih f' g') f g

/--
**Weak Two-Function Hypercontractivity on a Single Bit.**
For `f, g : BoolCube 1 → ℝ`, and exponents `1 ≤ p ≤ 2`, `1 ≤ q ≤ 2`, setting
`ρ = √((p − 1)(q − 1))`:
  `⟨f, T_ρ g⟩ ≤ (𝔼[|f|^p])^{1/p} · (𝔼[|g|^q])^{1/q}`
-/
theorem weak_two_function_hypercontractivity_one_bit
    (p q : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (f g : BooleanFunc 1) :
    innerProduct f (noiseOp (Real.sqrt ((p - 1) * (q - 1))) g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) *
    (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
  -- Step 1: Factor the noise parameter √((p-1)(q-1)) = √(p-1) · √(q-1)
  have hp_sub : 0 ≤ p - 1 := by linarith
  have hq_sub : 0 ≤ q - 1 := by linarith
  have h_sqrt_factor : Real.sqrt ((p - 1) * (q - 1)) = Real.sqrt (p - 1) * Real.sqrt (q - 1) := by
    exact Real.sqrt_mul hp_sub (q - 1)
  -- Step 2: Rewrite using semigroup property T_{ab} = T_a ∘ T_b
  have h_compose : noiseOp (Real.sqrt ((p - 1) * (q - 1))) g =
      noiseOp (Real.sqrt (p - 1)) (noiseOp (Real.sqrt (q - 1)) g) := by
    rw [h_sqrt_factor, ← noiseOp_compose]
  rw [h_compose]
  -- Step 3: Use self-adjointness: ⟨f, T_{√(p-1)} h⟩ = ⟨T_{√(p-1)} f, h⟩
  rw [← noiseOp_self_adjoint]
  -- Step 4: Apply Cauchy-Schwarz
  have h_cs := cauchy_schwarz_bool (noiseOp (Real.sqrt (p - 1)) f) (noiseOp (Real.sqrt (q - 1)) g)
  -- Step 5: Apply one-bit (p,2)-hypercontractivity to each factor
  have h_hyp_f : (expect (fun x => (noiseOp (Real.sqrt (p - 1)) f x) ^ 2)) ^ ((1 : ℝ) / 2) ≤
      (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
    exact one_bit_p2_hypercontractivity p hp1 hp2 (Real.sqrt (p - 1))
      (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt hp_sub])
      f
  have h_hyp_g : (expect (fun x => (noiseOp (Real.sqrt (q - 1)) g x) ^ 2)) ^ ((1 : ℝ) / 2) ≤
      (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
    exact one_bit_p2_hypercontractivity q hq1 hq2 (Real.sqrt (q - 1))
      (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt hq_sub])
      g
  -- Chain the inequalities
  calc innerProduct (noiseOp (Real.sqrt (p - 1)) f) (noiseOp (Real.sqrt (q - 1)) g)
      ≤ (expect (fun x => (noiseOp (Real.sqrt (p - 1)) f x) ^ 2)) ^ ((1 : ℝ) / 2) *
        (expect (fun x => (noiseOp (Real.sqrt (q - 1)) g x) ^ 2)) ^ ((1 : ℝ) / 2) := h_cs
    _ ≤ (expect (fun x => |f x| ^ p)) ^ (1 / p) *
        (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
        apply mul_le_mul h_hyp_f h_hyp_g
        · exact Real.rpow_nonneg (expect_sq_noiseOp_nonneg _ _) _
        · exact Real.rpow_nonneg (expect_rpow_abs_nonneg _ _) _

/-! ## Main Theorem -/
/-We first prove the equivalence of two function and one function hypercontractivity so
that we can transfer our easier results from two function to the one function case.
We utilize the weak two-function case to obtain the bridging one-function, then
prove the remaining one-function cases to obtain the general one function result.
-/

/-- **Two function to one function**
One function (p, q) hypercontractivity iff two-function (p, q') hypercontractivity -/
theorem one_function_iff_two_function_hypercontractivity {n : ℕ} (p q : ℝ)
    (hp1 : 1 ≤ p) (hpq : p ≤ q) (hq : 2 ≤ q)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (q - 1))) :
    -- One-function hypercontractivity
    (∀ f : BooleanFunc n,
      (expect (fun x => |noiseOp ρ f x| ^ q)) ^ (1 / q) ≤
      (expect (fun x => |f x| ^ p)) ^ (1 / p))
    ↔
    -- Two-function hypercontractivity (dual form)
    (∀ (f g : BooleanFunc n),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ (q / (q - 1)))) ^ ((q - 1) / q) *
      (expect (fun x => |g x| ^ p)) ^ (1 / p)) := by
  constructor;
  · intro h f g;
    have h_holder : ⟪f, noiseOp ρ g⟫_𝔹 ≤ (expect (fun x => |f x| ^ (q / (q - 1)))) ^ ((q - 1) / q) * (expect (fun x => |noiseOp ρ g x| ^ q)) ^ (1 / q) := by
      convert holder_ineq_bool ( q / ( q - 1 ) ) ( by rw [ lt_div_iff₀ ] <;> linarith ) f ( noiseOp ρ g ) using 1;
      grind;
    exact h_holder.trans ( mul_le_mul_of_nonneg_left ( h g ) ( Real.rpow_nonneg ( by exact expect_rpow_abs_nonneg (q / (q - 1)) f) _ ) );
  · intro h f;
    -- By the sharpness of Hölder's inequality, there exists some $f$ such that $\|f\|_{q'} \leq 1$ and $\langle f, T_\rho g \rangle \geq \|T_\rho g\|_q$.
    obtain ⟨f', hf'_norm, hf'_inner⟩ : ∃ f' : BooleanFunc n, (expect (fun x => |f' x| ^ (q / (q - 1)))) ^ ((q - 1) / q) ≤ 1 ∧ (expect (fun x => f' x * (noiseOp ρ f x))) ≥ (expect (fun x => |noiseOp ρ f x| ^ q)) ^ (1 / q) := by
      have := @holder_sharpness n ( q / ( q - 1 ) ) q ?_ ( fun x => noiseOp ρ f x ) <;> norm_num at *;
      · obtain ⟨ f', hf'₁, hf'₂ ⟩ := this; use f'; simp_all +decide [ BooleanAnalysis.innerProduct ] ;
      · constructor <;> norm_num;
        · rw [ inv_eq_one_div, ← add_div, div_eq_iff ] <;> linarith;
        · exact div_pos ( by linarith ) ( by linarith );
        · linarith;
    exact hf'_inner.trans ( h f' f |> le_trans <| mul_le_of_le_one_left ( by exact Real.rpow_nonneg ( by exact expect_nonneg_of_nonneg fun _ => by positivity ) _ ) hf'_norm )

/--
**Weak Two-Function Hypercontractivity**
For `f, g : BoolCube n → ℝ`, and exponents `1 ≤ p ≤ 2`, `1 ≤ q ≤ 2`, setting
`ρ = √((p − 1)(q − 1))`:
  `⟨f, T_ρ g⟩ ≤ (𝔼[|f|^p])^{1/p} · (𝔼[|g|^q])^{1/q}`
-/
theorem weak_two_function_hypercontractivity
    (p q : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    {n : ℕ} (f g : BooleanFunc n) :
    innerProduct f (noiseOp (Real.sqrt ((p - 1) * (q - 1))) g) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) *
    (expect (fun x => |g x| ^ q)) ^ (1 / q) := by
  have ρ_nonneg : 0 ≤ Real.sqrt ((p - 1) * (q - 1)) := by
    apply Real.sqrt_nonneg
  have p_sub : 0 ≤ p - 1 := by linarith
  have q_sub : 0 ≤ q - 1 := by linarith
  have p_le_one : p - 1 ≤ 1 := by linarith
  have q_le_one : q - 1 ≤ 1 := by linarith
  have ρ_le_one : Real.sqrt ((p - 1) * (q - 1)) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith
  apply hypercontractivity_induction p q hp1 hq1 (Real.sqrt ((p - 1) * (q - 1))) (ρ_nonneg) (ρ_le_one)
        (weak_two_function_hypercontractivity_one_bit p q hp1 hp2 hq1 hq2) f g

/-
The noise kernel sums to 1 over the second argument.
-/
lemma noiseKernel_sum_right {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (x : BoolCube n) : ∑ y : BoolCube n, noiseKernel ρ x y = 1 := by
  unfold noiseKernel;
  -- The sum over y factorizes as a product of independent sums over each bit.
  have h_factor : ∑ y : BoolCube n, (∏ i : Fin n, (1 + ρ * boolToSign (x i) * boolToSign (y i)) / 2) = ∏ i : Fin n, ∑ y : Bool, (1 + ρ * boolToSign (x i) * boolToSign y) / 2 := by
    exact Eq.symm (Fintype.prod_sum fun i j => (1 + ρ * boolToSign (x i) * boolToSign j) / 2);
  rw [ h_factor, Finset.prod_eq_one ] ; intros ; norm_num [ Finset.sum_div _ _ _, boolToSign ] ; ring

/-
The noise kernel sums to 1 over the first argument (doubly stochastic).
-/
lemma noiseKernel_sum_left {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (y : BoolCube n) : ∑ x : BoolCube n, noiseKernel ρ x y = 1 := by
  convert noiseKernel_sum_right hρ0 hρ1 y using 1;
  unfold noiseKernel; congr; ext; ring_nf;
  ac_rfl

/-
Jensen's inequality applied to the noise kernel: for convex `|·|^s` with `s ≥ 1`,
`|T_ρ f(x)|^s ≤ ∑_y K_ρ(x,y) |f(y)|^s`.
-/
lemma noiseOp_abs_rpow_le_kernel_avg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (s : ℝ) (hs : 1 ≤ s) (f : BooleanFunc n) (x : BoolCube n) :
    |noiseOp ρ f x| ^ s ≤ ∑ y : BoolCube n, noiseKernel ρ x y * |f y| ^ s := by
  have h_triangle : |noiseOp ρ f x| ≤ ∑ y : BoolCube n, noiseKernel ρ x y * |f y| := by
    rw [ noiseOp_eq_kernel_sum ];
    exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun y _ => by rw [ abs_mul, abs_of_nonneg ( noiseKernel_nonneg hρ0 hρ1 x y ) ] );
  have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ s) := by
    exact ( convexOn_rpow ( by linarith ) );
  refine' le_trans ( Real.rpow_le_rpow ( abs_nonneg _ ) h_triangle ( by positivity ) ) _;
  convert h_jensen.map_sum_le _ _ _ <;> norm_num;
  · exact fun y => noiseKernel_nonneg hρ0 hρ1 x y;
  · exact noiseKernel_sum_right hρ0 hρ1 x

/-
For any `s ≥ 1` and `0 ≤ ρ ≤ 1`, the noise operator is a contraction on Lˢ.
Uses Jensen's inequality on the noise kernel and the doubly stochastic property.
-/
lemma trivial_contractivity {n : ℕ} (s : ℝ) (hs : 1 ≤ s)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : BooleanFunc n) :
    (expect (fun x => |noiseOp ρ f x| ^ s)) ^ (1 / s) ≤
    (expect (fun x => |f x| ^ s)) ^ (1 / s) := by
  -- Using the inequality |T_ρ f(x)|^s ≤ ∑_y K(x,y) |f(y)|^s from `noiseOp_abs_rpow_le_kernel_avg`.
  have h_ineq : ∀ x : BoolCube n, |noiseOp ρ f x|^s ≤ ∑ y : BoolCube n, noiseKernel ρ x y * |f y|^s := by
    exact fun x => noiseOp_abs_rpow_le_kernel_avg hρ0 hρ1 s hs f x;
  refine' Real.rpow_le_rpow ( mul_nonneg ( by exact pow_nonneg ( by norm_num ) _ ) ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( abs_nonneg _ ) _ ) ) ( mul_le_mul_of_nonneg_left _ ( by exact pow_nonneg ( by norm_num ) _ ) ) ( by positivity );
  refine' le_trans ( Finset.sum_le_sum fun x _ => h_ineq x ) _;
  rw [ Finset.sum_comm ];
  simp +decide [← Finset.sum_mul, noiseKernel_sum_left hρ0 hρ1 ]

/-
Duality / Adjointness of operator norms
-/
lemma noise_op_norm_dual {n : ℕ} (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∀ f : BooleanFunc n,
      (expect (fun x => |noiseOp ρ f x| ^ q)) ^ (1 / q) ≤
      (expect (fun x => |f x| ^ p)) ^ (1 / p))
    ↔
    (∀ f : BooleanFunc n,
      (expect (fun x => |noiseOp ρ f x| ^ (p / (p - 1)))) ^ ((p - 1) / p) ≤
      (expect (fun x => |f x| ^ (q / (q - 1)))) ^ ((q - 1) / q)) := by
  constructor <;> intro h;
  · intro f
    have h_dual : ∀ g : BooleanFunc n, innerProduct g (noiseOp ρ f) ≤ (expect (fun x => |g x| ^ p)) ^ (1 / p) * (expect (fun x => |f x| ^ (q / (q - 1)))) ^ ((q - 1) / q) := by
      intro g
      have := h g
      have := h f
      simp_all;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right ( h g ) _ );
      · convert holder_ineq_bool q hq ( noiseOp ρ g ) f using 1;
        · exact Eq.symm (noiseOp_self_adjoint ρ g f);
        · grind +splitImp;
      · exact Real.rpow_nonneg ( expect_rpow_abs_nonneg _ _ ) _;
    have := @holder_sharpness n ( p := p ) ( q := p / ( p - 1 ) ) ?_ ( noiseOp ρ f ) <;> norm_num at *;
    · obtain ⟨ g, hg₁, hg₂ ⟩ := this; exact hg₂.trans ( h_dual g |> le_trans <| mul_le_of_le_one_left ( by exact Real.rpow_nonneg ( by exact expect_rpow_abs_nonneg _ _ ) _ ) hg₁ ) ;
    · exact (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl;
  · intro f
    have h_dual : ∀ g : BooleanFunc n, innerProduct g (noiseOp ρ f) ≤ (expect (fun x => |g x| ^ (q / (q - 1)))) ^ ((q - 1) / q) * (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
      -- Apply the hypothesis `h` to the function `g`.
      intros g
      have := h g;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right this _ );
      · have := @holder_ineq_bool n ( p / ( p - 1 ) ) ?_ ( noiseOp ρ g ) f;
        · convert this using 1;
          · exact Eq.symm (noiseOp_self_adjoint ρ g f);
          · congr 1
            · congr 1
              have : p ≠ 0 := by linarith
              have : p - 1 ≠ 0 := by linarith
              field_simp;
            · congr 1
              · congr 1  -- <-- ADDED: Strips `expect`, leaving `(fun x => ...) = (fun x => ...)`
                ext x
                congr 1  -- Strips `|f x| ^`, leaving the exponent equality
                have : p ≠ 0 := by linarith
                have : p - 1 ≠ 0 := by linarith
                field_simp; ring
              · have : p ≠ 0 := by linarith
                have : p - 1 ≠ 0 := by linarith
                field_simp; ring
        · rw [ lt_div_iff₀ ] <;> linarith;
      · exact Real.rpow_nonneg ( expect_rpow_abs_nonneg _ _ ) _;
    have := @holder_sharpness n ( p := q / ( q - 1 ) ) ( q := q ) ?_ ( noiseOp ρ f ) <;> norm_num at *;
    · obtain ⟨ g, hg₁, hg₂ ⟩ := this; exact hg₂.trans ( h_dual g |> le_trans <| mul_le_of_le_one_left ( by exact Real.rpow_nonneg ( by exact expect_rpow_abs_nonneg _ _ ) _ ) hg₁ ) ;
    · constructor <;> norm_num [ hp, hq ];
      · rw [ inv_eq_one_div, ← add_div, div_eq_iff ] <;> linarith;
      · positivity;
      · positivity

private lemma sqrt_div_le_one {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    Real.sqrt (a / b) ≤ 1 := by
  rw [Real.sqrt_le_one]
  exact div_le_one_iff.mpr (Or.inl ⟨hb, hab⟩)
private lemma noise_param_eq {p u : ℝ} (hu_pos : 0 < u - 1) :
    (u / (u - 1) - 1) * (p - 1) = (p - 1) / (u - 1) := by
  field_simp; ring
/--
**Bridging Case of One-Function Hypercontractivity.**
For `1 ≤ p ≤ 2 ≤ u` and `ρ = √((p-1)/(u-1))`:
  `(𝔼[|T_ρ f|^u])^{1/u} ≤ (𝔼[|f|^p])^{1/p}`
Derived by using `weak_two_function_hypercontractivity` with `p' = u/(u-1)` and `q' = p`
to get the two-function bound, then applying the backward direction of
`one_function_iff_two_function_hypercontractivity`.
-/
theorem bridging_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (hu : 2 ≤ u) (f : BooleanFunc n) :
    (expect (fun x => |noiseOp (Real.sqrt ((p - 1) / (u - 1))) f x| ^ u)) ^ (1 / u) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  set ρ := Real.sqrt ((p - 1) / (u - 1)) with hρ_def
  have hu_pos : 0 < u - 1 := by linarith
  have hp_sub : 0 ≤ p - 1 := by linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := sqrt_div_le_one hp_sub hu_pos (by linarith)
  have hu'1 : 1 ≤ u / (u - 1) := le_div_iff₀ hu_pos |>.mpr (by linarith)
  have hu'2 : u / (u - 1) ≤ 2 := div_le_iff₀ hu_pos |>.mpr (by linarith)
  have h_noise_eq : Real.sqrt ((u / (u - 1) - 1) * (p - 1)) = ρ := by
    congr 1; exact noise_param_eq hu_pos
  have h_two_func : ∀ (f g : BooleanFunc n),
      innerProduct f (noiseOp ρ g) ≤
      (expect (fun x => |f x| ^ (u / (u - 1)))) ^ ((u - 1) / u) *
      (expect (fun x => |g x| ^ p)) ^ (1 / p) := by
    intro f' g'
    have h := weak_two_function_hypercontractivity (u / (u - 1)) p hu'1 hu'2 hp1 hp2 f' g'
    rw [h_noise_eq] at h
    convert h using 2
    · congr 1; field_simp
  exact ((one_function_iff_two_function_hypercontractivity p u hp1 (le_trans hp2 hu) hu
    ρ hρ0 hρ1 (le_refl _)).mpr h_two_func) f

/-
Algebraic helper: all interpolation constraints for the low norms case.
Given `1 < p < u < 2` and `ρ² = (p-1)/(u-1)`, there exist `θ ∈ (0,1)` and `s > 0`
such that the interpolation equations hold.
Concretely, `θ = 2(u+p-2)/(pu)` and `s = 2-p`.
-/
private lemma low_norms_interpolation_params (p u ρ : ℝ) (hp : 1 < p) (hpu : p < u) (hu : u < 2)
    (hρ_sq : ρ ^ 2 = (p - 1) / (u - 1)) :
    ∃ θ s : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < s ∧
    1 / p = θ / (1 + ρ ^ 2) + (1 - θ) / s ∧
    1 / u = θ / 2 + (1 - θ) / s := by
  refine' ⟨ 2 * ( u + p - 2 ) / ( p * u ), 2 - p, _, _, _, _, _ ⟩ <;> try nlinarith;
  · exact div_pos ( by linarith ) ( by nlinarith );
  · rw [ div_lt_iff₀ ] <;> nlinarith;
  · grind +splitIndPred;
  · grind

/-! ## General Two-Point Inequality (Unit Case)
The key real-analysis inequality needed for the (p, q) one-bit hypercontractivity.
-/
/-- The average M(b) = ((1+b)^p + (1-b)^p)/2 is at least 1 for b ∈ [0,1] and p ≥ 1. -/
lemma avg_rpow_ge_one {p b : ℝ} (hp : 1 ≤ p) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    1 ≤ ((1 + b) ^ p + (1 - b) ^ p) / 2 := by
  have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ p) := convexOn_rpow (by linarith)
  have := h_jensen.2 (show 0 ≤ 1 + b by linarith) (show 0 ≤ 1 - b by linarith)
  convert @this (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) using 1 <;>
    norm_num <;> ring_nf
  norm_num

/-
For a convex function f on [0, ∞) and 0 ≤ x ≤ y with 1+x, 1-x, 1+y, 1-y ≥ 0:
    f(1+y) + f(1-y) ≥ f(1+x) + f(1-x).
-/
lemma convex_sym_sum_mono {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    f (1 + x) + f (1 - x) ≤ f (1 + y) + f (1 - y) := by
  by_cases hxy' : x < y;
  · -- For 0 ≤ x < y ≤ 1, apply the secant_mono lemma with a = 1-y, x = 1-x, y = 1+y.
    have h1 : (f (1 - x) - f (1 - y)) / (y - x) ≤ (f (1 + y) - f (1 - y)) / (2 * y) := by
      convert hf.secant_mono _ _ _ _ _ using 1 <;> norm_num;
      rotate_left;
      exact 1 - y;
      exact 1 - x;
      exact 1 + y;
      exacts [ by linarith, by linarith, by linarith, by linarith, by linarith, by rw [ show 1 - x - ( 1 - y ) = y - x by ring, show 1 + y - ( 1 - y ) = 2 * y by ring ] ; exact ⟨ fun h => fun _ => h, fun h => h ( by linarith ) ⟩ ];
    have := hf.slope_mono_adjacent ( show 0 ≤ 1 - y by linarith ) ( show 0 ≤ 1 + y by linarith ) ( show 1 - y < 1 + x by linarith ) ( show 1 + x < 1 + y by linarith ) ; norm_num at * ; rw [ div_le_div_iff₀ ] at * <;> nlinarith;
  · rw [ le_antisymm hxy ( not_lt.mp hxy' ) ]

/-
For 0 < b < 1, the function α ↦ b^α is convex (exponential with base < 1).
-/
lemma rpow_sum_antitone_exponent {p q : ℝ} {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hp0 : p ≤ 0) (hpq : p ≤ q) (hq0 : q ≤ 0) :
    (1 + x) ^ p + (1 - x) ^ p ≥ (1 + x) ^ q + (1 - x) ^ q := by
  by_contra! h_contra;
  -- Let's define the function \( f(t) = (1 + x)^t + (1 - x)^t \) and show that its derivative is non-positive on \((-\infty, 0]\).
  set f : ℝ → ℝ := fun t => (1 + x)^t + (1 - x)^t
  have hf_deriv_nonpos : ∀ t < 0, deriv f t ≤ 0 := by
    intro t ht; norm_num [ f, Real.rpow_def_of_pos ( by linarith : 0 < 1 + x ), Real.rpow_def_of_pos ( by linarith : 0 < 1 - x ), mul_comm ];
    -- Since $t < 0$, we have $t * \log(1 + x) < 0$ and $t * \log(1 - x) > 0$.
    have h_exp_neg : Real.exp (t * Real.log (1 + x)) ≤ 1 ∧ Real.exp (t * Real.log (1 - x)) ≥ 1 := by
      exact ⟨ Real.exp_le_one_iff.mpr ( mul_nonpos_of_nonpos_of_nonneg ht.le ( Real.log_nonneg ( by linarith ) ) ), Real.one_le_exp ( mul_nonneg_of_nonpos_of_nonpos ht.le ( Real.log_nonpos ( by linarith ) ( by linarith ) ) ) ⟩;
    nlinarith [ Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 + x ), Real.log_le_sub_one_of_pos ( by linarith : 0 < 1 - x ), Real.exp_pos ( t * Real.log ( 1 + x ) ), Real.exp_pos ( t * Real.log ( 1 - x ) ) ];
  -- Since $f$ is differentiable and its derivative is non-positive on $(-\infty, 0]$, we can apply the Mean Value Theorem to $f$ on the interval $[p, q]$.
  have h_mvt : ∃ c ∈ Set.Ioo p q, deriv f c = (f q - f p) / (q - p) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hpq.lt_of_ne ( by rintro rfl; linarith );
    · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.add ( ContinuousAt.rpow continuousAt_const continuousAt_id <| Or.inl <| by linarith ) ( ContinuousAt.rpow continuousAt_const continuousAt_id <| Or.inl <| by linarith );
    · exact DifferentiableOn.add ( DifferentiableOn.rpow ( differentiableOn_const _ ) differentiableOn_id ( by intro t ht; linarith ) ) ( DifferentiableOn.rpow ( differentiableOn_const _ ) differentiableOn_id ( by intro t ht; linarith ) );
  obtain ⟨ c, ⟨ hpc, hcq ⟩, hcd ⟩ := h_mvt; have := hf_deriv_nonpos c ( by linarith ) ; rw [ hcd, div_le_iff₀ ] at this <;> linarith;

/-
Key derivative inequality for the two-point inequality.
-/
lemma h_alpha_ineq {r s c t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1)
    (hc : c = Real.sqrt (r / s)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + t) ^ r - (1 - t) ^ r ≥ c * ((1 + c * t) ^ s - (1 - c * t) ^ s) := by
  by_cases hr0 : r = 0;
  · aesop;
  · -- Let's define the function $g(t)$ and show that its derivative is non-negative on $(0,1)$.
    set g : ℝ → ℝ := fun t => (1 + t)^r - (1 - t)^r - c * ((1 + c * t)^s - (1 - c * t)^s)
    have hg_deriv_nonneg : ∀ t ∈ Set.Ioo 0 1, 0 ≤ deriv g t := by
      -- Let's simplify the expression for the derivative.
      have h_deriv_simplified : ∀ t ∈ Set.Ioo 0 1, deriv g t = r * ((1 + t)^(r - 1) + (1 - t)^(r - 1) - (c^2 * s / r) * ((1 + c * t)^(s - 1) + (1 - c * t)^(s - 1))) := by
        intro t ht;
        convert HasDerivAt.deriv ( HasDerivAt.sub ( HasDerivAt.sub ( HasDerivAt.rpow_const ( hasDerivAt_id' t |> HasDerivAt.const_add _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' t |> HasDerivAt.const_sub _ ) _ ) ) ( HasDerivAt.const_mul c ( HasDerivAt.sub ( HasDerivAt.rpow_const ( HasDerivAt.const_add _ ( hasDerivAt_id' t |> HasDerivAt.const_mul _ ) ) _ ) ( HasDerivAt.rpow_const ( HasDerivAt.const_sub _ ( hasDerivAt_id' t |> HasDerivAt.const_mul _ ) ) _ ) ) ) ) using 1 <;> norm_num;
        · grind;
        · exact Or.inl <| by linarith [ ht.1 ] ;
        · exact Or.inl <| by linarith [ ht.1, ht.2 ] ;
        · exact Or.inl ( by nlinarith [ ht.1, ht.2, show 0 ≤ c by rw [ hc ] ; positivity ] );
        · exact Or.inl ( by nlinarith [ ht.1, ht.2, show c ≤ 1 by rw [ hc ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith [ show 0 < r by positivity ] ⟩ ] );
      -- Since $c^2 * s / r = 1$, we can simplify the expression for the derivative.
      have h_deriv_simplified' : ∀ t ∈ Set.Ioo 0 1, deriv g t = r * ((1 + t)^(r - 1) + (1 - t)^(r - 1) - ((1 + c * t)^(s - 1) + (1 - c * t)^(s - 1))) := by
        intro t ht; rw [ h_deriv_simplified t ht ] ; rw [ hc ] ; rw [ Real.sq_sqrt <| div_nonneg hr <| by linarith ] ; ring_nf;
        grind +splitImp;
      -- Since $r \leq s$, we have $(1 + t)^{r-1} + (1 - t)^{r-1} \geq (1 + c * t)^{s-1} + (1 - c * t)^{s-1}$ for $t \in (0, 1)$.
      have h_ineq : ∀ t ∈ Set.Ioo 0 1, (1 + t)^(r - 1) + (1 - t)^(r - 1) ≥ (1 + c * t)^(s - 1) + (1 - c * t)^(s - 1) := by
        intros t ht
        have h_ineq_step1 : (1 + t)^(r - 1) + (1 - t)^(r - 1) ≥ (1 + t)^(s - 1) + (1 - t)^(s - 1) := by
          exact rpow_sum_antitone_exponent ht.1 ht.2 ( by linarith ) ( by linarith ) ( by linarith );
        have h_ineq_step2 : (1 + t)^(s - 1) + (1 - t)^(s - 1) ≥ (1 + c * t)^(s - 1) + (1 - c * t)^(s - 1) := by
          have h_deriv_nonneg : ∀ x ∈ Set.Ioo 0 t, deriv (fun x => (1 + x)^(s - 1) + (1 - x)^(s - 1)) x ≥ 0 := by
            intros x hx
            have h_deriv : deriv (fun x => (1 + x)^(s - 1) + (1 - x)^(s - 1)) x = (s - 1) * ((1 + x)^(s - 2) - (1 - x)^(s - 2)) := by
              convert HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.rpow_const ( hasDerivAt_id' x |> HasDerivAt.const_add _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' x |> HasDerivAt.const_sub _ ) _ ) ) using 1 <;> norm_num <;> ring_nf;
              · exact Or.inl <| by linarith [ hx.1 ] ;
              · exact Or.inl <| by linarith [ hx.1, hx.2, ht.1, ht.2 ] ;
            exact h_deriv.symm ▸ mul_nonneg_of_nonpos_of_nonpos ( by linarith ) ( sub_nonpos_of_le ( by rw [ Real.rpow_le_rpow_iff_of_neg ] <;> linarith [ hx.1, hx.2, ht.1, ht.2 ] ) )
          by_cases h_cases : c * t < t;
          · have := exists_deriv_eq_slope ( f := fun x => ( 1 + x ) ^ ( s - 1 ) + ( 1 - x ) ^ ( s - 1 ) ) h_cases;
            contrapose! this;
            simp +zetaDelta at *;
            refine' ⟨ _, _, _ ⟩;
            · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.add ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.1, show 0 ≤ c * t by exact mul_nonneg ( hc.symm ▸ Real.sqrt_nonneg _ ) ht.1.le ] ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inl <| by linarith [ hx.2, show c * t < t by linarith ] );
            · exact DifferentiableOn.add ( DifferentiableOn.rpow ( differentiableOn_id.const_add _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1, hx.2, show 0 ≤ c * t by exact mul_nonneg ( hc.symm ▸ Real.sqrt_nonneg _ ) ht.1.le ] ) ) ( DifferentiableOn.rpow ( differentiableOn_id.const_sub _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1, hx.2, show 0 ≤ c * t by exact mul_nonneg ( hc.symm ▸ Real.sqrt_nonneg _ ) ht.1.le ] ) );
            · intro x hx₁ hx₂; rw [ eq_div_iff ] <;> nlinarith [ h_deriv_nonneg x ( by nlinarith [ show 0 ≤ c by rw [ hc ] ; positivity ] ) hx₂ ] ;
          · norm_num [ show c = 1 by nlinarith [ ht.1, ht.2, show 0 ≤ c by rw [ hc ] ; positivity, show c ≤ 1 by rw [ hc ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith [ show 0 < s by exact lt_of_lt_of_le ( lt_of_le_of_ne hr ( Ne.symm hr0 ) ) hrs ] ⟩ ] ] at *;
        linarith;
      exact fun t ht => h_deriv_simplified' t ht ▸ mul_nonneg hr ( sub_nonneg_of_le ( h_ineq t ht ) );
    by_contra h_contra;
    -- Apply the mean value theorem to the interval $[0, t]$.
    obtain ⟨ξ, hξ⟩ : ∃ ξ ∈ Set.Ioo 0 t, deriv g ξ = (g t - g 0) / (t - 0) := by
      apply_rules [ exists_deriv_eq_slope ];
      · exact ht0.lt_of_ne ( by rintro rfl; norm_num [ hr0 ] at h_contra );
      · refine' ContinuousOn.sub _ _;
        · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inr <| by positivity ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inr <| by positivity ) ;
        · refine' ContinuousOn.mul continuousOn_const _;
          refine' ContinuousOn.sub _ _;
          · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.rpow ( continuousAt_const.add ( continuousAt_const.mul continuousAt_id ) ) continuousAt_const <| Or.inr <| by linarith [ show 0 < s by exact lt_of_lt_of_le ( by positivity ) hrs ] ;
          · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.rpow ( continuousAt_const.sub ( continuousAt_const.mul continuousAt_id ) ) continuousAt_const <| Or.inr <| by linarith [ show 0 < s by exact lt_of_lt_of_le ( by positivity ) hrs ] ;
      · refine' DifferentiableOn.sub _ _;
        · exact DifferentiableOn.sub ( DifferentiableOn.rpow ( differentiableOn_id.const_add _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.1 ] ) ) ( DifferentiableOn.rpow ( differentiableOn_id.const_sub _ ) ( differentiableOn_const _ ) ( by intro x hx; linarith [ hx.2 ] ) );
        · refine' DifferentiableOn.mul _ _;
          · exact differentiableOn_const _;
          · refine' DifferentiableOn.sub _ _;
            · exact DifferentiableOn.rpow ( DifferentiableOn.add ( differentiableOn_const _ ) ( differentiableOn_id.const_mul _ ) ) ( differentiableOn_const _ ) ( by intro x hx; exact ne_of_gt ( add_pos_of_pos_of_nonneg zero_lt_one ( mul_nonneg ( hc.symm ▸ Real.sqrt_nonneg _ ) hx.1.le ) ) );
            · exact DifferentiableOn.rpow ( DifferentiableOn.sub ( differentiableOn_const _ ) ( differentiableOn_id.const_mul _ ) ) ( differentiableOn_const _ ) ( by intro x hx; exact ne_of_gt ( sub_pos.mpr ( by nlinarith [ hx.1, hx.2, show c ≤ 1 by rw [ hc ] ; exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith [ show 0 < r by positivity ] ⟩ ] ) ) );
    simp +zetaDelta at *;
    rw [ eq_div_iff ] at hξ <;> nlinarith [ hg_deriv_nonneg ξ hξ.1.1 ( by linarith ) ]

/-
The integrated form of h_alpha_ineq via MVT.
From h_alpha_ineq we know that for 0 ≤ r ≤ s ≤ 1, c = √(r/s), 0 ≤ t ≤ 1:
  (1+t)^r - (1-t)^r ≥ c * ((1+ct)^s - (1-ct)^s)
Integrating (via MVT) from 0 to b gives:
  ((1+b)^(r+1) + (1-b)^(r+1) - 2)/(r+1) ≥ ((1+cb)^(s+1) + (1-cb)^(s+1) - 2)/(s+1)
-/
lemma integrated_h_alpha_ineq {p q b : ℝ} (hp1 : 1 ≤ p) (hpq : p ≤ q) (hq2 : q ≤ 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    let ρ := Real.sqrt ((p - 1) / (q - 1))
    ((1 + ρ * b) ^ q + (1 - ρ * b) ^ q - 2) / q ≤
    ((1 + b) ^ p + (1 - b) ^ p - 2) / p := by
      -- Define the function g(t) and show that its derivative is non-negative.
      set ρ := Real.sqrt ((p - 1) / (q - 1))
      set g : ℝ → ℝ := fun t => ((1 + t) ^ p + (1 - t) ^ p - 2) / p - ((1 + ρ * t) ^ q + (1 - ρ * t) ^ q - 2) / q
      have hg_deriv_nonneg : ∀ t ∈ Set.Ioo 0 b, 0 ≤ deriv g t := by
        -- By definition of $g$, we can compute its derivative.
        have hg_deriv : ∀ t ∈ Set.Ioo 0 b, deriv g t = ((1 + t) ^ (p - 1) - (1 - t) ^ (p - 1)) - ρ * ((1 + ρ * t) ^ (q - 1) - (1 - ρ * t) ^ (q - 1)) := by
          intro t ht; refine' HasDerivAt.deriv _; convert HasDerivAt.sub ( HasDerivAt.div_const ( HasDerivAt.sub ( HasDerivAt.add
          ( HasDerivAt.rpow_const ( hasDerivAt_id' t |> HasDerivAt.const_add _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_id' t |>
          HasDerivAt.const_sub _ ) _ ) ) ( hasDerivAt_const _ _ ) ) _ ) ( HasDerivAt.div_const ( HasDerivAt.sub ( HasDerivAt.add ( HasDerivAt.rpow_const
          ( HasDerivAt.const_add _ ( HasDerivAt.const_mul _ ( hasDerivAt_id' t ) ) ) _ ) ( HasDerivAt.rpow_const ( HasDerivAt.const_sub _ ( HasDerivAt.const_mul _
          ( hasDerivAt_id' t ) ) ) _ ) ) ( hasDerivAt_const _ _ ) ) _ ) using 1 <;> norm_num [ show p ≠ 0 by linarith, show q ≠ 0 by linarith ] ; ring_nf;
          · simp +decide [ mul_assoc, mul_comm p, mul_left_comm q, ne_of_gt ( zero_lt_one.trans_le hp1 ), ne_of_gt ( zero_lt_one.trans_le ( by linarith : 1 ≤ q ) ) ];
          · exact Or.inl <| by linarith [ ht.1 ] ;
          · exact Or.inl <| by linarith [ ht.1, ht.2 ] ;
          · exact Or.inl <| by nlinarith [ ht.1, ht.2, Real.sqrt_nonneg ( ( p - 1 ) / ( q - 1 ) ) ] ;
          · exact Or.inr ( by linarith );
        have := @h_alpha_ineq;
        intro t ht; specialize this ( show 0 ≤ p - 1 by linarith ) ( show p - 1 ≤ q - 1 by linarith ) ( show q - 1 ≤ 1 by linarith ) rfl ( show 0 ≤ t by linarith [ ht.1 ] ) ( show t ≤ 1 by linarith [ ht.2 ] ) ; aesop;
      by_cases hb : b = 0;
      · norm_num [ hb ];
      · have := exists_deriv_eq_slope g ( show b > 0 from lt_of_le_of_ne hb0 ( Ne.symm hb ) );
        simp +zetaDelta at *;
        contrapose! this;
        refine' ⟨ _, _, _ ⟩;
        · refine' ContinuousOn.sub _ _;
          · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div ( ContinuousAt.sub ( ContinuousAt.add ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ) continuousAt_const ) continuousAt_const <| by linarith;
          · refine' ContinuousOn.div_const _ _;
            refine' ContinuousOn.sub _ continuousOn_const;
            exact ContinuousOn.add ( ContinuousOn.rpow ( continuousOn_const.add ( continuousOn_const.mul continuousOn_id ) ) continuousOn_const <| by intro t ht; exact Or.inr <| by linarith ) ( ContinuousOn.rpow ( continuousOn_const.sub ( continuousOn_const.mul continuousOn_id ) ) continuousOn_const <| by intro t ht; exact Or.inr <| by linarith );
        · refine' fun t ht => DifferentiableAt.differentiableWithinAt _;
          apply_rules [ DifferentiableAt.sub, DifferentiableAt.div, DifferentiableAt.add, DifferentiableAt.rpow_const ] <;> norm_num [ add_comm, mul_comm ];
          any_goals contrapose! hb; linarith;
          · exact differentiableAt_id.const_mul _;
          · exact differentiableAt_id.const_mul _;
        · intro c hc; rw [ ne_eq, eq_div_iff ] <;> norm_num <;> nlinarith [ hg_deriv_nonneg c hc.1 hc.2 ] ;

/-
Tangent line inequality for x^r at x = 1: for x ≥ 0, r ≥ 1, x^r ≥ 1 + r*(x-1).
-/
lemma rpow_ge_one_add_mul_sub {x r : ℝ} (hx : 0 ≤ x) (hr : 1 ≤ r) :
    x ^ r ≥ 1 + r * (x - 1) := by
      have := @Real.geom_mean_le_arith_mean;
      specialize this { 0, 1 } ( fun i => if i = 0 then 1 else r - 1 ) ( fun i => if i = 0 then x ^ r else 1 ) ; norm_num at *;
      specialize this hr ( by positivity ) ( by positivity ) ; rw [ ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ] at this ; rw [ le_div_iff₀ ( by positivity ) ] at this ; nlinarith;

/-
The general two-point inequality in the unit case.
Proved using integrated_h_alpha_ineq and rpow_ge_one_add_mul_sub,
without circular dependence on low_norms_hypercontractivity.
-/
theorem two_point_ineq_general_unit (b p q : ℝ) (hp1 : 1 ≤ p) (hpq : p ≤ q) (hq2 : q ≤ 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    let ρ := Real.sqrt ((p - 1) / (q - 1))
    ((1 + ρ * b) ^ q + (1 - ρ * b) ^ q) / 2 ≤
    (((1 + b) ^ p + (1 - b) ^ p) / 2) ^ (q / p) := by
      by_cases hq : q = 0 <;> by_cases hp : p = 0 <;> simp_all +decide [ mul_comm, div_eq_mul_inv ];
      · norm_num at *;
      · linarith;
      · linarith;
      · have := @integrated_h_alpha_ineq p q b hp1 hpq hq2 hb0 hb1;
        have := @rpow_ge_one_add_mul_sub ( ( ( 1 + b ) ^ p + ( 1 - b ) ^ p ) / 2 ) ( q / p ) ?_ ?_ <;> norm_num at *;
        · field_simp at *;
          rw [ div_le_iff₀ ( by linarith ) ] at this;
          rw [ Real.sqrt_div ( by linarith ) ] at * ; ring_nf at * ; nlinarith [ mul_inv_cancel_left₀ hp q ] ;
        · exact div_nonneg ( add_nonneg ( Real.rpow_nonneg ( by linarith ) _ ) ( Real.rpow_nonneg ( by linarith ) _ ) ) zero_le_two;
        · rw [ le_div_iff₀ ] <;> linarith

/-! ## One-Bit Low Norms Hypercontractivity -/
/-
One-bit (p, q)-hypercontractivity for 1 < p ≤ q ≤ 2.
Uses the general two-point inequality applied to the Fourier coefficients.
This is proved WITHOUT using general_one_function_hypercontractivity (to avoid circularity).
-/
theorem low_norms_one_bit (p q : ℝ) (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 2)
    (f : BooleanFunc 1) :
    (expect (fun x => |noiseOp (Real.sqrt ((p - 1) / (q - 1))) f x| ^ q)) ^ (1 / q) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  -- Use the one-bit structure directly with two_point_ineq_general_unit
  set a := fourierCoeff f ∅
  set b := fourierCoeff f {⟨0, by omega⟩}
  set ρ := Real.sqrt ((p - 1) / (q - 1))
  -- Rewrite the Lp norm of f
  rw [expect_abs_rpow_one_bit p f]
  -- For the noise-operated function, we need its Lq norm
  -- The noise operator on one-bit functions: noiseOp ρ f has values a+ρb and a-ρb
  rw [expect_abs_rpow_one_bit q (noiseOp ρ f)]
  -- Now the goal involves Fourier coefficients of noiseOp ρ f
  -- fourierCoeff (noiseOp ρ f) ∅ = a and fourierCoeff (noiseOp ρ f) {0} = ρ * b
  -- After simplification, the goal becomes:
  -- ((|a + ρb|^q + |a - ρb|^q)/2)^{1/q} ≤ ((|a + b|^p + |a - b|^p)/2)^{1/p}
  -- This is the general two-point inequality
  -- Apply the general two-point inequality to the Fourier coefficients.
  have h_two_point : ((|a + ρ * b| ^ q + |a - ρ * b| ^ q) / 2) ^ (1 / q) ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (1 / p) := by
    -- Without loss of generality, assume $b \geq 0$.
    suffices h_wlog : ∀ {a b : ℝ}, 0 ≤ b → ((|a + ρ * b| ^ q + |a - ρ * b| ^ q) / 2) ^ (1 / q) ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (1 / p) by
      cases le_total 0 b <;> simp_all +decide [ abs_sub_comm ];
      convert @h_wlog a ( -b ) ( by linarith ) using 1 <;> norm_num [ abs_sub_comm ];
      · ring_nf;
      · ring_nf;
    intro a b hb_nonneg
    suffices h_wlog : ∀ {a b : ℝ}, 0 ≤ b → 0 ≤ a → ((|a + ρ * b| ^ q + |a - ρ * b| ^ q) / 2) ^ (1 / q) ≤ ((|a + b| ^ p + |a - b| ^ p) / 2) ^ (1 / p) by
      cases abs_cases a <;> simp +decide [ * ];
      · simpa using h_wlog hb_nonneg ( by linarith );
      · convert h_wlog hb_nonneg ( neg_nonneg.mpr ( by linarith : a ≤ 0 ) ) using 1 <;> norm_num [ abs_sub_comm ];
        · rw [ show -a + ρ * b = - ( a - ρ * b ) by ring, show -a - ρ * b = - ( a + ρ * b ) by ring, abs_neg, abs_neg ] ; ring_nf;
        · congr 1; congr 1; rw [show |-a + b| = |a - b| from by rw [show -a + b = -(a - b) from by ring, abs_neg]]; rw [add_comm]; rw [show |a + b| = |b + a| from by rw [add_comm]]
    intro a b hb_nonneg ha_nonneg
    by_cases hab : a ≥ b;
    · by_cases ha : a = 0;
      · simp_all +decide [ show b = 0 by linarith ];
        norm_num [ show q ≠ 0 by linarith, show p ≠ 0 by linarith ];
      · -- Let $t = \frac{b}{a}$, then $0 \leq t \leq 1$.
        set t := b / a
        have ht : 0 ≤ t ∧ t ≤ 1 := by
          exact ⟨ div_nonneg hb_nonneg ha_nonneg, div_le_one_of_le₀ hab ha_nonneg ⟩;
        -- Apply the general two-point inequality to $t$.
        have h_two_point : ((|1 + ρ * t| ^ q + |1 - ρ * t| ^ q) / 2) ^ (1 / q) ≤ ((|1 + t| ^ p + |1 - t| ^ p) / 2) ^ (1 / p) := by
          have := @two_point_ineq_general_unit;
          convert Real.rpow_le_rpow _ ( this t p q hp.le hpq hq ht.1 ht.2 ) ( show 0 ≤ 1 / q by exact one_div_nonneg.mpr ( by linarith ) ) using 1;
          · rw [ abs_of_nonneg, abs_of_nonneg ] <;> norm_num;
            · exact le_trans ( mul_le_of_le_one_right ( Real.sqrt_nonneg _ ) ht.2 ) ( Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> nlinarith ⟩ );
            · exact add_nonneg zero_le_one ( mul_nonneg ( Real.sqrt_nonneg _ ) ht.1 );
          · rw [ ← Real.rpow_mul ( by exact div_nonneg ( add_nonneg ( Real.rpow_nonneg ( by linarith ) _ ) ( Real.rpow_nonneg ( by linarith ) _ ) ) zero_le_two ), mul_comm ] ; ring_nf ; norm_num [ show p ≠ 0 by linarith, show q ≠ 0 by linarith ];
            rw [ abs_of_nonneg ( by linarith ), abs_of_nonneg ( by linarith ) ];
          · exact div_nonneg ( add_nonneg ( Real.rpow_nonneg ( by nlinarith [ Real.sqrt_nonneg ( ( p - 1 ) / ( q - 1 ) ) ] ) _ ) ( Real.rpow_nonneg ( by nlinarith [ Real.sqrt_nonneg ( ( p - 1 ) / ( q - 1 ) ), show Real.sqrt ( ( p - 1 ) / ( q - 1 ) ) * t ≤ 1 by exact mul_le_one₀ ( Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith ⟩ ) ht.1 ht.2 ] ) _ ) ) zero_le_two;
        convert mul_le_mul_of_nonneg_left h_two_point ( show 0 ≤ |a| by positivity ) using 1 <;> norm_num [ abs_div, abs_mul, abs_of_nonneg, ha_nonneg, hb_nonneg, ha ];
        · rw [ show a + ρ * b = a * ( 1 + ρ * t ) by rw [ mul_add, mul_left_comm, mul_div_cancel₀ _ ha ] ; ring, show a - ρ * b = a * ( 1 - ρ * t ) by rw [ mul_sub, mul_left_comm, mul_div_cancel₀ _ ha ] ; ring, abs_mul, abs_mul, abs_of_nonneg ha_nonneg ] ; ring_nf;
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
          rw [ show a ^ q * |1 + ρ * t| ^ q * ( 1 / 2 ) + a ^ q * |1 - ρ * t| ^ q * ( 1 / 2 ) = a ^ q * ( |1 + ρ * t| ^ q * ( 1 / 2 ) + |1 - ρ * t| ^ q * ( 1 / 2 ) ) by ring, Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by linarith ), Real.rpow_one ];
        · rw [ show a + b = a * ( 1 + t ) by rw [ mul_add, mul_div_cancel₀ _ ha ] ; ring, show a - b = a * ( 1 - t ) by rw [ mul_sub, mul_div_cancel₀ _ ha ] ; ring, abs_mul, abs_mul, abs_of_nonneg ha_nonneg ];
          rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ];
          rw [ show ( a ^ p * |1 + t| ^ p + a ^ p * |1 - t| ^ p ) / 2 = a ^ p * ( ( |1 + t| ^ p + |1 - t| ^ p ) / 2 ) by ring, Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ), mul_inv_cancel₀ ( by positivity ), Real.rpow_one ];
    · -- Since $a < b$, we have $|a + \rho b| \leq |b + \rho a|$ and $|a - \rho b| \leq |b - \rho a|$.
      have h_abs : |a + ρ * b| ≤ |b + ρ * a| ∧ |a - ρ * b| ≤ |b - ρ * a| := by
        constructor <;> rw [ abs_le ] <;> constructor <;> cases abs_cases ( b + ρ * a ) <;> cases abs_cases ( b - ρ * a ) <;> nlinarith [ show 0 ≤ ρ by positivity, show ρ ≤ 1 by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith ⟩ ];
      have h_abs_pow : |a + ρ * b| ^ q + |a - ρ * b| ^ q ≤ |b + ρ * a| ^ q + |b - ρ * a| ^ q := by
        exact add_le_add ( Real.rpow_le_rpow ( abs_nonneg _ ) h_abs.1 ( by linarith ) ) ( Real.rpow_le_rpow ( abs_nonneg _ ) h_abs.2 ( by linarith ) );
      have h_abs_pow : ((|b + ρ * a| ^ q + |b - ρ * a| ^ q) / 2) ^ (1 / q) ≤ ((|b + a| ^ p + |b - a| ^ p) / 2) ^ (1 / p) := by
        have := @two_point_ineq_general_unit;
        specialize this ( a / b ) p q ( by linarith ) ( by linarith ) ( by linarith ) ( by positivity ) ( by rw [ div_le_iff₀ ( by linarith ) ] ; linarith );
        by_cases hb : b = 0 <;> simp_all +decide;
        convert Real.rpow_le_rpow ( by positivity ) ( show ( ( |b + ρ * a| ^ q + |b - ρ * a| ^ q ) / 2 ) ≤ ( ( |b + a| ^ p + |b - a| ^ p ) / 2 ) ^ ( q / p ) from ?_ ) ( show 0 ≤ q⁻¹ by exact inv_nonneg.mpr ( by linarith ) ) using 1;
        · rw [ ← Real.rpow_mul ( by positivity ) ] ; ring_nf ; norm_num [ show q ≠ 0 by linarith ];
        · convert mul_le_mul_of_nonneg_left this ( show 0 ≤ b ^ q by positivity ) using 1 <;> ring_nf;
          · rw [ show b + ρ * a = b * ( 1 + a * ρ * b⁻¹ ) by nlinarith [ mul_inv_cancel_left₀ hb ( a * ρ ) ], show b - ρ * a = b * ( 1 - a * ρ * b⁻¹ ) by nlinarith [ mul_inv_cancel_left₀ hb ( a * ρ ) ], abs_of_nonneg ( by positivity ), abs_of_nonneg ( by nlinarith [ mul_inv_cancel_left₀ hb ( a * ρ ), show ρ ≤ 1 by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> nlinarith ⟩ ] ) ] ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by nlinarith [ mul_inv_cancel_left₀ hb ( a * ρ ), show ρ ≤ 1 by exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ div_le_iff₀ ] <;> nlinarith ⟩ ] ) ] ; ring_nf;
            grind;
          · rw [ show |b + a| = b + a by rw [ abs_of_nonneg ] ; linarith, show |b - a| = b - a by rw [ abs_of_nonneg ] ; linarith ] ; ring_nf;
            rw [ show b + a = b * ( 1 + a / b ) by rw [ mul_add, mul_div_cancel₀ _ hb ] ; ring, show b - a = b * ( 1 - a / b ) by rw [ mul_sub, mul_div_cancel₀ _ hb ] ; ring, Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by exact sub_nonneg.mpr <| div_le_one_of_le₀ ( by linarith ) <| by positivity ) ] ; ring_nf;
            rw [ show b ^ p * ( 1 + a * b⁻¹ ) ^ p * ( 1 / 2 ) + b ^ p * ( 1 - a * b⁻¹ ) ^ p * ( 1 / 2 ) = b ^ p * ( ( 1 + a * b⁻¹ ) ^ p * ( 1 / 2 ) + ( 1 - a * b⁻¹ ) ^ p * ( 1 / 2 ) ) by ring, Real.mul_rpow ( by positivity ) ( by exact add_nonneg ( mul_nonneg ( Real.rpow_nonneg ( by nlinarith [ mul_inv_cancel₀ hb ] ) _ ) ( by positivity ) ) ( mul_nonneg ( Real.rpow_nonneg ( by nlinarith [ mul_inv_cancel₀ hb ] ) _ ) ( by positivity ) ) ), ← Real.rpow_mul ( by positivity ), mul_comm ] ; ring_nf;
            norm_num [ show p ≠ 0 by linarith ];
      simp_all +decide [ add_comm, abs_sub_comm ];
      exact le_trans ( Real.rpow_le_rpow ( by positivity ) ( by linarith ) ( by exact inv_nonneg.mpr ( by linarith ) ) ) h_abs_pow;
  convert h_two_point using 3;
  unfold noiseOp; norm_num;
  unfold a b; unfold BooleanAnalysis.fourierCoeff; norm_num [ Finset.sum_range_succ, chiS ] ;
  unfold innerProduct;
  unfold expect; norm_num [ Finset.sum_range_succ, chiS ] ;
  unfold uniformWeight; norm_num [ Finset.sum_range_succ, chiS ] ;
  rw [ show ( Finset.univ : Finset ( Finset ( Fin 1 ) ) ) = { ∅, { 0 } } by decide ] ; simp +decide [Finset.prod_singleton, boolToSign ] ; ring_nf;
  rw [ show ( Finset.univ : Finset ( BoolCube 1 ) ) = { fun _ => Bool.true, fun _ => Bool.false } by decide ] ; simp +decide [Finset.sum_singleton ] ; ring_nf;
-- NEEDS: non-circular proof of two-point inequality for general (a, b, p, q, ρ)

/--
**Low Norms Hypercontractivity.**
For `1 < p ≤ u ≤ 2` and `ρ = √((p-1)/(u-1))`:
  `(𝔼[|T_ρ f|^u])^{1/u} ≤ (𝔼[|f|^p])^{1/p}`
-/
theorem low_norms_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp : 1 < p) (hpu : p ≤ u) (hu : u ≤ 2)
    (f : BooleanFunc n) :
    (expect (fun x => |noiseOp (Real.sqrt ((p - 1) / (u - 1))) f x| ^ u)) ^ (1 / u) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  set ρ := Real.sqrt ((p - 1) / (u - 1)) with hρ_def
  have hu1 : 1 < u := lt_of_lt_of_le hp hpu
  have hp_sub : 0 < p - 1 := by linarith
  have hu_sub : 0 < u - 1 := by linarith
  have hρ_sq : ρ ^ 2 = (p - 1) / (u - 1) := by
    rw [hρ_def]; exact Real.sq_sqrt (div_nonneg hp_sub.le hu_sub.le)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := sqrt_div_le_one hp_sub.le hu_sub (by linarith)
  -- Case 1: p = u (trivial contractivity)
  by_cases h_eq : p = u
  · subst h_eq
    have hρ_eq_1 : ρ = 1 := by rw [hρ_def]; simp [div_self (ne_of_gt hu_sub)]
    rw [hρ_eq_1]
    exact trivial_contractivity p (by linarith) 1 (by norm_num) (by norm_num) f  -- p > 1 ≥ 1
  · have hpu_strict : p < u := lt_of_le_of_ne hpu h_eq
    -- Case 2: u = 2 (bridging case applies directly)
    by_cases hu2 : u = 2
    · subst hu2
      exact bridging_hypercontractivity p 2 (by linarith) (by linarith) (by norm_num) f
    · -- Case 3: p < u < 2
      -- This requires the general two-point inequality for (p, u) norms.
      -- The proof proceeds by induction on n using a one-bit base case.
            -- Step 1: One-bit one-function
      have h_one_bit : ∀ g : BooleanFunc 1,
          (expect (fun x => |noiseOp ρ g x| ^ u)) ^ (1 / u) ≤
          (expect (fun x => |g x| ^ p)) ^ (1 / p) := by
        intro g; exact low_norms_one_bit p u hp hpu hu g
      -- Step 2: One-bit two-function (via Hölder)
      have h_two_func_one : ∀ (f' g' : BooleanFunc 1),
          innerProduct f' (noiseOp ρ g') ≤
          (expect (fun x => |f' x| ^ (u / (u - 1)))) ^ ((u - 1) / u) *
          (expect (fun x => |g' x| ^ p)) ^ (1 / p) := by
        intros f' g';
        refine' le_trans _ ( mul_le_mul_of_nonneg_left ( h_one_bit g' ) ( Real.rpow_nonneg ( expect_rpow_abs_nonneg _ _ ) _ ) );
        convert holder_ineq_bool ( u / ( u - 1 ) ) ( by rw [ lt_div_iff₀ ] <;> linarith ) f' ( noiseOp ρ g' ) using 1;
        grind  -- Hölder + h_one_bit
      -- Step 3: N-bit two-function (via hypercontractivity_induction)
      have hu' : 1 ≤ u / (u - 1) := le_div_iff₀ hu_sub |>.mpr (by linarith)
      have h_two_func_n : ∀ (f' g' : BooleanFunc n),
          innerProduct f' (noiseOp ρ g') ≤
          (expect (fun x => |f' x| ^ (u / (u - 1)))) ^ ((u - 1) / u) *
          (expect (fun x => |g' x| ^ p)) ^ (1 / p) := by
        intro f' g'
        have h_base : ∀ (f₁ g₁ : BooleanFunc 1),
            innerProduct f₁ (noiseOp ρ g₁) ≤
            (expect (fun x => |f₁ x| ^ (u / (u - 1)))) ^ (1 / (u / (u - 1))) *
            (expect (fun x => |g₁ x| ^ p)) ^ (1 / p) := by
          intro f₁ g₁
          convert h_two_func_one f₁ g₁ using 2; congr 1; field_simp
        convert hypercontractivity_induction (u / (u - 1)) p hu' (by linarith) ρ hρ0 hρ1 h_base f' g' using 2
        congr 1; field_simp
      -- Step 4: N-bit one-function (via Hölder sharpness)
      obtain ⟨f', hf'_norm, hf'_inner⟩ : ∃ f' : BooleanFunc n,
          (expect (fun x => |f' x| ^ (u / (u - 1)))) ^ ((u - 1) / u) ≤ 1 ∧
          (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u) ≤ innerProduct f' (noiseOp ρ f) := by
        have := @holder_sharpness n (u / (u - 1)) u ?_ (noiseOp ρ f)
        · obtain ⟨f', hf'₁, hf'₂⟩ := this; use f'
          refine ⟨?_, hf'₂⟩
          have : (1 : ℝ) / (u / (u - 1)) = (u - 1) / u := by field_simp
          rwa [this] at hf'₁
        · constructor <;> norm_num
          · rw [inv_eq_one_div, ← add_div, div_eq_iff] <;> linarith
          · exact div_pos (by linarith) (by linarith)
          · linarith
      exact hf'_inner.trans (le_trans (h_two_func_n f' f)
        (mul_le_of_le_one_left (Real.rpow_nonneg (expect_nonneg_of_nonneg fun _ => by positivity) _) hf'_norm))
/--
**High Norms Hypercontractivity.**
For `2 ≤ p ≤ u` and `ρ ≤ √((p-1)/(u-1))`:
  `(𝔼[|T_ρ f|^u])^{1/u} ≤ (𝔼[|f|^p])^{1/p}`
Proof by duality: translating to the Hölder-conjugate exponents `u' ≤ p' ≤ 2`
and applying the low-norms case.
-/
theorem high_norms_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp : 2 ≤ p) (hpu : p ≤ u)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (u - 1)))
    (f : BooleanFunc n) :
    (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  set p' := p / (p - 1) with hp'_def
  set u' := u / (u - 1) with hu'_def
  have hp1 : 1 < p := by linarith
  have hu1 : 1 < u := by linarith
  have hp_sub : 0 < p - 1 := by linarith
  have hu_sub : 0 < u - 1 := by linarith
  have hp'_gt1 : 1 < p' := by rw [hp'_def, lt_div_iff₀ hp_sub]; linarith
  have hp'_le2 : p' ≤ 2 := by rw [hp'_def, div_le_iff₀ hp_sub]; linarith
  have hu'_gt1 : 1 < u' := by rw [hu'_def, lt_div_iff₀ hu_sub]; linarith
  have hu'_le_p' : u' ≤ p' := by
    rw [hu'_def, hp'_def, div_le_div_iff₀ hu_sub hp_sub]; nlinarith
  have h_conj_param : (p - 1) / (u - 1) = (u' - 1) / (p' - 1) := by
    rw [hp'_def, hu'_def]; field_simp; ring
  set ρ₀ := Real.sqrt ((p - 1) / (u - 1))
  have hρ₀0 : 0 ≤ ρ₀ := Real.sqrt_nonneg _
  have hρ₀1 : ρ₀ ≤ 1 := sqrt_div_le_one hp_sub.le hu_sub (by linarith)
  -- Low norms: ‖T_{ρ₀}‖_{u'→p'} ≤ 1
  have h_low : ∀ g : BooleanFunc n,
      (expect (fun x => |noiseOp ρ₀ g x| ^ p')) ^ (1 / p') ≤
      (expect (fun x => |g x| ^ u')) ^ (1 / u') := by
    intro g
    rw [show ρ₀ = Real.sqrt ((u' - 1) / (p' - 1)) from by rw [← h_conj_param]]
    exact low_norms_hypercontractivity u' p' hu'_gt1 hu'_le_p' hp'_le2 g
  -- Duality
  have h_dual := (noise_op_norm_dual u' p' hu'_gt1 hp'_gt1 ρ₀ hρ₀0 hρ₀1).mp h_low
  have h_ρ₀_result : (expect (fun x => |noiseOp ρ₀ f x| ^ u)) ^ (1 / u) ≤
      (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
    have h := h_dual f
    have hp'_conj : p' / (p' - 1) = p := by rw [hp'_def]; field_simp; ring
    have hu'_conj : u' / (u' - 1) = u := by rw [hu'_def]; field_simp; ring
    have hp'_exp : (p' - 1) / p' = 1 / p := by rw [hp'_def]; field_simp; ring
    have hu'_exp : (u' - 1) / u' = 1 / u := by rw [hu'_def]; field_simp; ring
    rw [hp'_conj, hu'_conj, hp'_exp, hu'_exp] at h
    exact h
  -- For ρ ≤ ρ₀: composition + contractivity
  by_cases hρ₀_zero : ρ₀ = 0
  · have : ρ = 0 := le_antisymm (by rw [← hρ₀_zero]; exact hρ_bound) hρ0
    rw [this]; rw [hρ₀_zero] at h_ρ₀_result; exact h_ρ₀_result
  · have hρ₀_pos : 0 < ρ₀ := lt_of_le_of_ne hρ₀0 (Ne.symm hρ₀_zero)
    have h_compose : noiseOp ρ f = noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) := by
      rw [noiseOp_compose, div_mul_cancel₀ _ (ne_of_gt hρ₀_pos)]
    have h_contract := trivial_contractivity u (by linarith : 1 ≤ u)
      (ρ / ρ₀) (div_nonneg hρ0 hρ₀0) (by rwa [div_le_one hρ₀_pos]) (noiseOp ρ₀ f)
    calc (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u)
        = (expect (fun x => |noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) x| ^ u)) ^ (1 / u) := by
          rw [h_compose]
      _ ≤ (expect (fun x => |noiseOp ρ₀ f x| ^ u)) ^ (1 / u) := h_contract
      _ ≤ (expect (fun x => |f x| ^ p)) ^ (1 / p) := h_ρ₀_result

/-! ## General One-Function Hypercontractivity -/

/-
**General One-Function Hypercontractivity Theorem.**
For `1 ≤ p ≤ u` with `u > 1` and `ρ ≤ √((p-1)/(u-1))`:
  `(𝔼[|T_ρ f|^u])^{1/u} ≤ (𝔼[|f|^p])^{1/p}`

Combines the three cases:
- Bridging: `1 ≤ p ≤ 2 ≤ u`
- Low norms: `1 < p ≤ u ≤ 2`
- High norms: `2 ≤ p ≤ u`
-/
theorem general_one_function_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp : 1 ≤ p) (hpu : p ≤ u) (hu1 : 1 < u)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (u - 1)))
    (f : BooleanFunc n) :
    (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u) ≤
    (expect (fun x => |f x| ^ p)) ^ (1 / p) := by
  by_cases hp2 : p ≤ 2
  · by_cases hu2 : 2 ≤ u
    · -- Case 1: 1 ≤ p ≤ 2 ≤ u (bridging + composition)
      set ρ₀ := Real.sqrt ((p - 1) / (u - 1))
      have hρ₀0 : 0 ≤ ρ₀ := Real.sqrt_nonneg _
      have hu_sub : 0 < u - 1 := by linarith
      have hρ₀1 : ρ₀ ≤ 1 := sqrt_div_le_one (by linarith) hu_sub (by linarith)
      by_cases hρ₀_zero : ρ₀ = 0
      · have hρz : ρ = 0 := le_antisymm (by rw [← hρ₀_zero]; exact hρ_bound) hρ0
        simp only [hρz]; show _ ≤ _
        rw [show (0 : ℝ) = ρ₀ from hρ₀_zero.symm]
        exact bridging_hypercontractivity p u hp hp2 hu2 f
      · have hρ₀_pos : 0 < ρ₀ := lt_of_le_of_ne hρ₀0 (Ne.symm hρ₀_zero)
        have h_compose : noiseOp ρ f = noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) := by
          rw [noiseOp_compose, div_mul_cancel₀ _ (ne_of_gt hρ₀_pos)]
        have h_contract := trivial_contractivity u (by linarith : 1 ≤ u)
          (ρ / ρ₀) (div_nonneg hρ0 hρ₀0) (by rwa [div_le_one hρ₀_pos]) (noiseOp ρ₀ f)
        calc (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u)
            = (expect (fun x => |noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) x| ^ u)) ^ (1 / u) := by
              rw [h_compose]
          _ ≤ (expect (fun x => |noiseOp ρ₀ f x| ^ u)) ^ (1 / u) := h_contract
          _ ≤ (expect (fun x => |f x| ^ p)) ^ (1 / p) :=
              bridging_hypercontractivity p u hp hp2 hu2 f
    · -- Case 2: 1 ≤ p ≤ u ≤ 2 (low norms)
      push_neg at hu2
      rcases eq_or_lt_of_le hp with rfl | hp1
      · -- p = 1 edge case: ρ = 0 and T_0 f is constant = E[f]
        simp only [sub_self, zero_div, Real.sqrt_zero] at hρ_bound
        have hρ_zero : ρ = 0 := le_antisymm hρ_bound hρ0
        subst hρ_zero
        -- T_0 f(x) = f̂(∅) for all x, so |T_0 f|^u is constant.
        -- By Jensen: E[|const|^u]^{1/u} = |const| ≤ E[|f|]^1
        -- This is trivial contractivity at s = u ≥ 1 with ρ = 0
        -- T_0 f is constant = E[f], so |T_0 f(x)|^u = |E[f]|^u.
        -- |E[f]| ≤ E[|f|] = ‖f‖_1 by triangle inequality.
        unfold noiseOp; norm_num;
        simp +decide [zero_pow_eq ];
        unfold expect; norm_num [ uniformWeight ] ;
        rw [ ← mul_assoc, ← mul_pow ] ; norm_num [ show u ≠ 0 by linarith ];
        unfold fourierCoeff;
        unfold innerProduct; norm_num [ uniformWeight ] ;
        unfold expect; norm_num [ uniformWeight ] ;
        exact Finset.abs_sum_le_sum_abs _ _ -- Edge case: p = 1, ρ = 0
      -- low_norms gives the bound with ρ = sqrt((p-1)/(u-1))
      -- For ρ ≤ that value, use composition + contractivity
      set ρ₀ := Real.sqrt ((p - 1) / (u - 1))
      have hρ₀0 : 0 ≤ ρ₀ := Real.sqrt_nonneg _
      have hu_sub : 0 < u - 1 := by linarith
      have hρ₀1 : ρ₀ ≤ 1 := sqrt_div_le_one (by linarith) hu_sub (by linarith)
      have h_low : ∀ g : BooleanFunc n,
          (expect (fun x => |noiseOp ρ₀ g x| ^ u)) ^ (1 / u) ≤
          (expect (fun x => |g x| ^ p)) ^ (1 / p) :=
        fun g => low_norms_hypercontractivity p u hp1 hpu (le_of_lt hu2) g
      by_cases hρ₀_zero : ρ₀ = 0
      · have : ρ = 0 := le_antisymm (by rw [← hρ₀_zero]; exact hρ_bound) hρ0
        rw [this]; rw [hρ₀_zero] at h_low; exact h_low f
      · have hρ₀_pos : 0 < ρ₀ := lt_of_le_of_ne hρ₀0 (Ne.symm hρ₀_zero)
        have h_compose : noiseOp ρ f = noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) := by
          rw [noiseOp_compose, div_mul_cancel₀ _ (ne_of_gt hρ₀_pos)]
        have h_contract := trivial_contractivity u (by linarith : 1 ≤ u)
          (ρ / ρ₀) (div_nonneg hρ0 hρ₀0) (by rwa [div_le_one hρ₀_pos]) (noiseOp ρ₀ f)
        calc (expect (fun x => |noiseOp ρ f x| ^ u)) ^ (1 / u)
            = (expect (fun x => |noiseOp (ρ / ρ₀) (noiseOp ρ₀ f) x| ^ u)) ^ (1 / u) := by
              rw [h_compose]
          _ ≤ (expect (fun x => |noiseOp ρ₀ f x| ^ u)) ^ (1 / u) := h_contract
          _ ≤ (expect (fun x => |f x| ^ p)) ^ (1 / p) := h_low f
  · -- Case 3: 2 ≤ p ≤ u (high norms)
    push_neg at hp2
    exact high_norms_hypercontractivity p u (le_of_lt hp2) hpu ρ hρ0 hρ1 hρ_bound f

/-! ## General Two-Function Hypercontractivity -/

/--
**General Two-Function Hypercontractivity Theorem.**
For `1 ≤ p ≤ u` with `u ≥ 2` and `ρ ≤ √((p-1)/(u-1))`:
  `⟨f, T_ρ g⟩ ≤ (𝔼[|f|^{u/(u-1)}])^{(u-1)/u} · (𝔼[|g|^p])^{1/p}`

Derived from the one-function theorem via `one_function_iff_two_function_hypercontractivity`.
-/
theorem general_two_function_hypercontractivity {n : ℕ}
    (p u : ℝ) (hp : 1 ≤ p) (hpu : p ≤ u) (hu : 2 ≤ u)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (u - 1)))
    (f g : BooleanFunc n) :
    innerProduct f (noiseOp ρ g) ≤
    (expect (fun x => |f x| ^ (u / (u - 1)))) ^ ((u - 1) / u) *
    (expect (fun x => |g x| ^ p)) ^ (1 / p) := by
  have hu1 : 1 < u := by linarith
  exact ((one_function_iff_two_function_hypercontractivity p u hp hpu hu ρ hρ0 hρ1 hρ_bound).mp
    (fun f' => general_one_function_hypercontractivity p u hp hpu hu1 ρ hρ0 hρ1 hρ_bound f')) f g

end GeneralHypercontractivity
