import TCSlib.BooleanAnalysis.Hypercontractivity.OneBit

open BooleanAnalysis OneBit Bonami SimpleHypercontractivity Real

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
    exact h_holder.trans ( mul_le_mul_of_nonneg_left ( h g ) ( Real.rpow_nonneg ( by exact? ) _ ) );
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

end GeneralHypercontractivity
