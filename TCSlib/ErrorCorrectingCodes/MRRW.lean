import Mathlib

/-!
# Formalization of the Binary First MRRW Bound

This file formalizes the content of `mrrw_bound_formalization_note.tex`,
a formalization-oriented proof note for the binary first
McEliece–Rodemich–Rumsey–Welch (MRRW) bound on the asymptotic binary code rate.

The main theorem states that for every `δ ∈ [0, 1/2]`,
  `R(δ) ≤ H(1/2 - √(δ(1-δ)))`
where `R` is the asymptotic binary code rate and `H` is the binary entropy function.

## Organization
The formalization follows the structure of the source document:
1. Basic definitions (maximum code size, binary entropy, asymptotic rate)
2. Krawtchouk polynomials and their properties
3. Delsarte's LP theorem
4. Christoffel–Darboux kernel and feasibility
5. Asymptotic analysis
6. Main MRRW bound
-/

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 800000

/-! ## Section 1: Statement and normalization

Corresponds to Section 1 of the source file, which defines the maximum code size,
asymptotic rate, and binary entropy, and states the main MRRW bound theorem.
-/

/-- **Definition 1 (maximum code size)** from the source file.
For integers `n ≥ 1` and `1 ≤ d ≤ n`, `codeA n d` denotes the maximum size of a
binary code `C ⊆ {0,1}^n` with minimum Hamming distance at least `d`.

The Hamming distance between two codewords is defined as the number of coordinates
at which they differ. -/
def codeA (n d : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (C : Finset (Fin n → Bool)),
    C.card = k ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      (Finset.univ.filter fun i => x i ≠ y i).card ≥ d}

/-- **Definition 3 (binary entropy)** from the source file.
`binaryEntropy x = -x · log₂(x) - (1-x) · log₂(1-x)`, with the convention
`0 · log₂ 0 = 0` (which holds automatically since `Real.logb 2 0 = 0`
in Mathlib).

Note: this uses base-2 logarithm (`Real.logb 2`), unlike Mathlib's
`Real.binEntropy` which uses natural logarithm. -/
def binaryEntropy (x : ℝ) : ℝ :=
  -x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x)

/-- **Definition 2 (asymptotic rate)** from the source file.
For `δ ∈ [0,1]`, `rate δ = limsup_{n→∞} (1/n) · log₂ A(n, ⌊δn⌋)`. -/
def rate (δ : ℝ) : ℝ :=
  Filter.limsup (fun (n : ℕ) =>
    Real.logb 2 ↑(codeA n ⌊δ * ↑n⌋₊) / (n : ℝ)) Filter.atTop

/-! ## Section 2: Krawtchouk polynomials

Corresponds to Section 2 of the source file, which defines binary Krawtchouk
polynomials and states their key properties: the generating function, special
value at zero, orthogonality, and three-term recurrence.
-/

/-- **Definition 4 (binary Krawtchouk polynomials, integer arguments)** from the
source file.
For `0 ≤ j ≤ n`, the binary Krawtchouk polynomial `K_j^{(n)}(x)` evaluated at
`x ∈ {0,1,...,n}` is given by
  `K_j^{(n)}(x) = ∑_{i=0}^{j} (-1)^i · C(x,i) · C(n-x, j-i)`.
This definition uses natural number subtraction; it gives the correct values
for `x ≤ n`. -/
def krawtchouk (n j x : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (-1 : ℝ) ^ i * (Nat.choose x i : ℝ) * (Nat.choose (n - x) (j - i) : ℝ)

/-- **Krawtchouk polynomials as actual polynomials over ℝ** (following the suggestion
of Remark 1 from the source file).
Defined via the three-term recurrence:
- `K_0(x) = 1`
- `K_1(x) = n - 2x`
- `(j+2) · K_{j+2}(x) = (n - 2x) · K_{j+1}(x) - (n - j) · K_j(x)`

This extends Definition 4 to real arguments as actual polynomials, enabling use
where real-valued arguments are needed (e.g., the Christoffel–Darboux identity). -/
def krawtchoukPoly (n : ℕ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.C (n : ℝ) - 2 * Polynomial.X
  | (j + 2) =>
    ((Polynomial.C (n : ℝ) - 2 * Polynomial.X) * krawtchoukPoly n (j + 1) -
     Polynomial.C ((n : ℝ) - ↑j) * krawtchoukPoly n j) *
     Polynomial.C (((j + 2 : ℕ) : ℝ)⁻¹)

/-
`K_0^{(n)}(x) = 1` for all `x`. This is immediate from Definition 4 of the
source file: the sum has only the `i = 0` term, giving
`(-1)^0 · C(x,0) · C(n-x,0) = 1`.
-/
theorem krawtchouk_zero (n x : ℕ) : krawtchouk n 0 x = 1 := by
  -- By definition of Krawtchouk polynomials, we know that $K_0^{(n)}(x) = 1$ for all $x$. This follows directly from the definition.
  simp [krawtchouk]

/-
**Lemma 2 (special value at zero)** from the source file.
For every `0 ≤ j ≤ n`, `K_j(0) = C(n,j)`. When `x = 0`, only the `i = 0` term
survives because `C(0, i) = 0` for `i > 0`.
-/
theorem krawtchouk_eval_zero (n j : ℕ) (hj : j ≤ n) :
    krawtchouk n j 0 = (Nat.choose n j : ℝ) := by
  unfold krawtchouk;
  simp +decide [ Finset.sum_range_succ', Nat.choose ]

/-
`K_1^{(n)}(x) = n - 2x` for `x ≤ n`. This follows from the definition of
Krawtchouk polynomials (Definition 4 of the source file) by expanding the
two-term sum: `C(n-x, 1) - C(x, 1) · C(n-x, 0) = (n - x) - x = n - 2x`.
-/
theorem krawtchouk_one (n x : ℕ) (hx : x ≤ n) :
    krawtchouk n 1 x = (n : ℝ) - 2 * (x : ℝ) := by
  unfold krawtchouk;
  norm_num [ Finset.sum_range_succ, hx ] ; ring

/-
**Lemma 1 (generating function)** from the source file.
For every `x ∈ {0,...,n}`,
  `∑_{j=0}^{n} K_j(x) · z^j = (1 - z)^x · (1 + z)^{n-x}`.
-/
theorem krawtchouk_generating_function (n x : ℕ) (hx : x ≤ n) (z : ℝ) :
    ∑ j ∈ Finset.range (n + 1), krawtchouk n j x * z ^ j =
      (1 - z) ^ x * (1 + z) ^ (n - x) := by
  -- The key identity is: ∑_{j=0}^{n} (∑_{i=0}^{j} (-1)^i C(x,i) C(n-x, j-i)) z^j = (1-z)^x (1+z)^{n-x}.
  have hKey : ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * Nat.choose x i * Nat.choose (n - x) (j - i) * z ^ j = (1 - z) ^ x * (1 + z) ^ (n - x) := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have hFubini : ∑ j ∈ Finset.range (n + 1), (∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * Nat.choose x i * Nat.choose (n - x) (j - i) * z ^ j) = ∑ i ∈ Finset.range (x + 1), (-1 : ℝ) ^ i * Nat.choose x i * (∑ j ∈ Finset.Ico i (n + 1), Nat.choose (n - x) (j - i) * z ^ j) := by
      have hFubini : ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (j + 1), (-1 : ℝ) ^ i * Nat.choose x i * Nat.choose (n - x) (j - i) * z ^ j = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.Ico i (n + 1), (-1 : ℝ) ^ i * Nat.choose x i * Nat.choose (n - x) (j - i) * z ^ j := by
        rw [ Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm ];
      rw [ hFubini, ← Finset.sum_subset ( Finset.range_mono ( Nat.succ_le_succ hx ) ) ];
      · simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
      · simp +contextual [ Nat.choose_eq_zero_of_lt ];
    -- Let's simplify the inner sum $\sum_{j=i}^{n} \binom{n-x}{j-i} z^j$.
    have hInner : ∀ i ∈ Finset.range (x + 1), ∑ j ∈ Finset.Ico i (n + 1), Nat.choose (n - x) (j - i) * z ^ j = z ^ i * (1 + z) ^ (n - x) := by
      intro i hi; rw [ add_comm 1 z, add_pow ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_Ico_eq_sum_range ] ;
      rw [ ← Finset.sum_subset ( Finset.range_mono ( show n - x + 1 ≤ n + 1 - i from by rw [ Nat.le_sub_iff_add_le ] <;> linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel hx ] ) ) ] <;> simp +decide [ pow_add, mul_assoc, mul_comm, mul_left_comm ];
      exact fun j hj₁ hj₂ => Or.inr <| Or.inr <| Nat.choose_eq_zero_of_lt hj₂;
    rw [ hFubini, Finset.sum_congr rfl fun i hi => by rw [ hInner i hi ] ];
    rw [ show ( 1 - z ) ^ x = ∑ i ∈ Finset.range ( x + 1 ), ( -1 : ℝ ) ^ i * Nat.choose x i * z ^ i by rw [ sub_eq_neg_add, add_pow ] ; congr ; ext ; ring ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, krawtchouk ]

/-
**Lemma 3 (orthogonality)** from the source file.
For `0 ≤ r, s ≤ n`,
  `∑_{x=0}^{n} C(n,x) · K_r(x) · K_s(x) = 2^n · C(n,r) · δ_{r,s}`.
-/
theorem krawtchouk_orthogonality (n r s : ℕ) (hr : r ≤ n) (hs : s ≤ n) :
    ∑ x ∈ Finset.range (n + 1),
      (Nat.choose n x : ℝ) * krawtchouk n r x * krawtchouk n s x =
      if r = s then 2 ^ n * (Nat.choose n r : ℝ) else 0 := by
  -- Consider the generating function $\sum_{x=0}^n \binom{n}{x} [(1-z)^x(1+z)^{n-x}] [(1-w)^x(1+w)^{n-x}]$.
  have h_gen_fun : ∀ z w : ℝ, ∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℝ) * ((1 - z) ^ x) * ((1 + z) ^ (n - x)) * ((1 - w) ^ x) * ((1 + w) ^ (n - x)) = ((1 + z) * (1 + w) + (1 - z) * (1 - w)) ^ n := by
    intro z w; rw [ add_comm, add_pow ] ; simp +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    rw [ add_comm, ← Finset.sum_flip ];
    exact Finset.sum_congr rfl fun x hx => by rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), tsub_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hx ) ] ;
  -- By equating the coefficients of $z^r w^s$ on both sides of the generating function equation, we obtain the desired orthogonality relation.
  have h_coeff : ∀ z w : ℝ, ∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℝ) * (∑ j ∈ Finset.range (n + 1), krawtchouk n j x * z ^ j) * (∑ k ∈ Finset.range (n + 1), krawtchouk n k x * w ^ k) = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), (∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℝ) * krawtchouk n j x * krawtchouk n k x) * z ^ j * w ^ k := by
    simp +decide only [mul_comm, Finset.mul_sum _ _ _, mul_left_comm];
    exact fun z w => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  -- By equating the coefficients of $z^r w^s$ on both sides of the generating function equation, we obtain the desired orthogonality relation. Hence, we can conclude the proof.
  have h_coeff_eq : ∀ z w : ℝ, ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), (∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℝ) * krawtchouk n j x * krawtchouk n k x) * z ^ j * w ^ k = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), (if j = k then 2 ^ n * (Nat.choose n j : ℝ) else 0) * z ^ j * w ^ k := by
    intros z w
    have h_eq : ∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℝ) * ((1 - z) ^ x) * ((1 + z) ^ (n - x)) * ((1 - w) ^ x) * ((1 + w) ^ (n - x)) = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), (if j = k then 2 ^ n * (Nat.choose n j : ℝ) else 0) * z ^ j * w ^ k := by
      rw [ h_gen_fun ];
      rw [ show ( 1 + z ) * ( 1 + w ) + ( 1 - z ) * ( 1 - w ) = 2 * ( 1 + z * w ) by ring ] ; rw [ mul_pow ] ; simp +decide [ add_comm, add_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ;
      exact Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range_succ_iff.mp hx ) ] ;
    rw [ ← h_coeff z w, ← h_eq ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ krawtchouk_generating_function n x ( Finset.mem_range_succ_iff.mp hx ) z, krawtchouk_generating_function n x ( Finset.mem_range_succ_iff.mp hx ) w ] ; ring;
  have h_coeff_eq : ∀ p : ℕ → ℕ → ℝ, (∀ z w : ℝ, ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1), p j k * z ^ j * w ^ k = 0) → ∀ j k : ℕ, j ≤ n → k ≤ n → p j k = 0 := by
    intros p hp j k hj hk;
    -- Fix $w$ and consider the polynomial in $z$.
    have h_poly_z : ∀ w : ℝ, ∀ j : ℕ, j ≤ n → ∑ k ∈ Finset.range (n + 1), p j k * w ^ k = 0 := by
      intros w j hj
      have h_poly_z : ∀ z : ℝ, ∑ j ∈ Finset.range (n + 1), (∑ k ∈ Finset.range (n + 1), p j k * w ^ k) * z ^ j = 0 := by
        exact fun z => by simpa only [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using hp z w;
      -- Since the polynomial in $z$ is zero for all $z$, its coefficients must be zero.
      have h_poly_zero : ∀ p : Polynomial ℝ, (∀ z : ℝ, p.eval z = 0) → ∀ j : ℕ, p.coeff j = 0 := by
        exact fun p hp j => by rw [ show p = 0 from Polynomial.funext fun x => by simpa using hp x ] ; norm_num;
      specialize h_poly_zero ( ∑ j ∈ Finset.range ( n + 1 ), ( ∑ k ∈ Finset.range ( n + 1 ), p j k * w ^ k ) • Polynomial.X ^ j ) ; simp_all +decide [ Polynomial.eval_finset_sum ];
    -- Fix $w$ and consider the polynomial in $z$. Since this polynomial is zero for all $w$, its coefficients must be zero.
    have h_poly_z_coeff : ∀ j : ℕ, j ≤ n → ∀ k : ℕ, k ≤ n → p j k = 0 := by
      intros j hj k hk;
      -- Consider the polynomial $P(w) = \sum_{k=0}^{n} p_{jk} w^k$.
      set P : Polynomial ℝ := Finset.sum (Finset.range (n + 1)) (fun k => Polynomial.C (p j k) * Polynomial.X ^ k);
      -- Since $P(w) = 0$ for all $w$, $P$ is the zero polynomial.
      have hP_zero : P = 0 := by
        simp +zetaDelta at *;
        exact Polynomial.funext fun x => by simpa [ Polynomial.eval_finset_sum ] using h_poly_z x j hj;
      replace hP_zero := congr_arg ( fun q => Polynomial.coeff q k ) hP_zero ; aesop;
    exact h_poly_z_coeff j hj k hk;
  specialize h_coeff_eq ( fun j k => ∑ x ∈ Finset.range ( n + 1 ), ( n.choose x : ℝ ) * krawtchouk n j x * krawtchouk n k x - if j = k then 2 ^ n * ( n.choose j : ℝ ) else 0 );
  simp_all +decide [ sub_mul ];
  exact eq_of_sub_eq_zero ( h_coeff_eq r s hr hs )

/-
**Lemma 4 (three-term recurrence)** from the source file.
For `1 ≤ j` and `j + 1 ≤ n`,
  `(j+1) · K_{j+1}(x) = (n - 2x) · K_j(x) - (n - j + 1) · K_{j-1}(x)`.
-/
theorem krawtchouk_recurrence (n j x : ℕ) (hj1 : 1 ≤ j) (hj2 : j + 1 ≤ n)
    (hx : x ≤ n) :
    ((j : ℝ) + 1) * krawtchouk n (j + 1) x =
      ((n : ℝ) - 2 * (x : ℝ)) * krawtchouk n j x -
      ((n : ℝ) - (j : ℝ) + 1) * krawtchouk n (j - 1) x := by
  have h_deriv : ∀ z : ℝ, deriv (fun z => ∑ j ∈ Finset.range (n + 1), (krawtchouk n j x : ℝ) * z ^ j) z = ∑ j ∈ Finset.range (n + 1), (krawtchouk n j x : ℝ) * j * z ^ (j - 1) := by
    norm_num [ mul_assoc ];
  have h_coeff : ∀ z : ℝ, (1 - z ^ 2) * ∑ j ∈ Finset.range (n + 1), (krawtchouk n j x : ℝ) * j * z ^ (j - 1) = ((n - 2 * x) - n * z) * ∑ j ∈ Finset.range (n + 1), (krawtchouk n j x : ℝ) * z ^ j := by
    intro z
    have h_poly : (1 - z ^ 2) * deriv (fun z => (1 - z) ^ x * (1 + z) ^ (n - x)) z = ((n - 2 * x) - n * z) * ((1 - z) ^ x * (1 + z) ^ (n - x)) := by
      erw [ deriv_mul ] <;> norm_num [ add_comm, sub_eq_add_neg ];
      · erw [ deriv_comp ] <;> norm_num [ neg_add_eq_sub ];
        · erw [ deriv_pow, deriv_sub ] <;> norm_num ; ring;
          cases le_iff_exists_add'.mp hx ; simp_all +decide [ Nat.succ_eq_add_one, pow_add ] ; ring;
          cases ‹ℕ› <;> cases x <;> norm_num [ pow_succ' ] ; ring;
          · ring;
          · ring;
        · exact DifferentiableAt.pow ( differentiableAt_id ) _;
        · exact differentiableAt_id.const_sub _;
      · exact DifferentiableAt.pow ( differentiableAt_id.neg.add_const _ ) _;
    convert h_poly using 1;
    · rw [ ← h_deriv, show ( fun z => ( 1 - z ) ^ x * ( 1 + z ) ^ ( n - x ) ) = fun z => ∑ j ∈ Finset.range ( n + 1 ), krawtchouk n j x * z ^ j from funext fun z => krawtchouk_generating_function n x hx z ▸ rfl ];
    · rw [ ← krawtchouk_generating_function n x hx z ];
  have h_coeff_eq : ∀ z : ℝ, ∑ j ∈ Finset.range (n + 1), (krawtchouk n j x : ℝ) * j * z ^ (j - 1) - ∑ j ∈ Finset.range (n + 1), (krawtchouk n j x : ℝ) * j * z ^ (j + 1) = (n - 2 * x) * ∑ j ∈ Finset.range (n + 1), (krawtchouk n j x : ℝ) * z ^ j - n * ∑ j ∈ Finset.range (n + 1), (krawtchouk n j x : ℝ) * z ^ (j + 1) := by
    convert h_coeff using 2 <;> ring;
    · norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, pow_succ' ] ; ring;
      rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_sub_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; cases ‹ℕ› <;> norm_num [ pow_succ' ] ; ring;
    · simpa only [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using by ring;
  have h_coeff_eq_poly : ∑ j ∈ Finset.range (n + 1), (Polynomial.C (krawtchouk n j x * j : ℝ) * Polynomial.X ^ (j - 1)) - ∑ j ∈ Finset.range (n + 1), (Polynomial.C (krawtchouk n j x * j : ℝ) * Polynomial.X ^ (j + 1)) = (Polynomial.C (n - 2 * x : ℝ) * ∑ j ∈ Finset.range (n + 1), (Polynomial.C (krawtchouk n j x : ℝ) * Polynomial.X ^ j)) - (Polynomial.C (n : ℝ) * ∑ j ∈ Finset.range (n + 1), (Polynomial.C (krawtchouk n j x : ℝ) * Polynomial.X ^ (j + 1))) := by
    exact sub_eq_iff_eq_add.mpr <| by exact Polynomial.funext fun z => by simpa [ Polynomial.eval_finset_sum ] using by linear_combination h_coeff_eq z;
  replace h_coeff_eq_poly := congr_arg ( fun p => Polynomial.coeff p ( j ) ) h_coeff_eq_poly ; norm_num [ Polynomial.coeff_C, Polynomial.coeff_X_pow ] at h_coeff_eq_poly ⊢;
  rcases j with ( _ | j ) <;> norm_num [ Finset.sum_range_succ', Polynomial.coeff_C, Polynomial.coeff_X_pow, mul_assoc ] at *;
  norm_num [ Polynomial.coeff_C, Polynomial.coeff_X_pow, mul_assoc, sub_mul, add_mul, Finset.sum_mul _ _ _ ] at h_coeff_eq_poly ⊢;
  grind

/-
**Consistency between sum formula and polynomial recurrence** (Remark 1 of the
source file).
For `x ≤ n`, evaluating `krawtchoukPoly n j` at `(x : ℝ)` agrees with
`krawtchouk n j x`. This justifies using either form interchangeably.
-/
theorem krawtchoukPoly_eval_nat (n j x : ℕ) (hj : j ≤ n) (hx : x ≤ n) :
    (krawtchoukPoly n j).eval (x : ℝ) = krawtchouk n j x := by
  induction' j using Nat.strong_induction_on with j ih generalizing x; rcases j with ( _ | _ | j ) <;> simp_all +decide [ krawtchoukPoly ] ;
  · exact (krawtchouk_zero n x).symm;
  · exact (krawtchouk_one n x hx).symm;
  · have := krawtchouk_recurrence n ( j + 1 ) x ( by linarith ) ( by linarith ) hx;
    grind

/-! ## Section 3: Delsarte's LP theorem

Corresponds to Theorem 2 and Remark 2 of the source file. The Delsarte linear
programming bound for the binary Hamming scheme.
-/

/-- **Theorem 2 (Delsarte LP inequality)** from the source file.
Let `F(x) = ∑_{j=0}^{n} F_j · K_j(x)` with real coefficients `F_j`. Assume:
1. `F_0 > 0`
2. `F_j ≥ 0` for all `1 ≤ j ≤ n`
3. `F(x) ≤ 0` for every integer `x ∈ {d, d+1, ..., n}`

Then `A(n,d) ≤ F(0)/F_0`.

As noted in Remark 2 of the source file, a Lean proof can be organized through the
distance distribution and the MacWilliams transform, without any asymptotic input. -/
theorem delsarte_lp_bound (n d : ℕ) (F : ℕ → ℝ)
    (hF0_pos : F 0 > 0)
    (hF_nonneg : ∀ j, 1 ≤ j → j ≤ n → F j ≥ 0)
    (hF_nonpos : ∀ x, d ≤ x → x ≤ n →
      ∑ j ∈ Finset.range (n + 1), F j * krawtchouk n j x ≤ 0) :
    (codeA n d : ℝ) ≤
      (∑ j ∈ Finset.range (n + 1), F j * krawtchouk n j 0) / F 0 := by
  sorry

/-! ## Section 4: Christoffel–Darboux kernel and feasibility

Corresponds to Section 3 of the source file, which introduces the truncated
reproducing kernel `Φ_{n,t}(a,x)`, the Christoffel–Darboux identity (Proposition 1),
and the feasibility region (Proposition 2).
-/

/-- **Christoffel–Darboux kernel** from Section 3 of the source file.
For `t ∈ {0,...,n}` and real parameters `a, x`, the truncated reproducing kernel is
  `Φ_{n,t}(a,x) = ∑_{j=0}^{t} K_j(a) · K_j(x) / C(n,j)`. -/
def cdKernel (n t : ℕ) (a x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (t + 1),
    (krawtchoukPoly n j).eval a * (krawtchoukPoly n j).eval x / (Nat.choose n j : ℝ)

/-
**Proposition 1 (Christoffel–Darboux identity for Krawtchouk)** from the source
file.
For `0 ≤ t ≤ n-1`, there exists a positive scalar `c > 0` such that
  `Φ_{n,t}(a,x) = c · (K_t(a) · K_{t+1}(x) - K_{t+1}(a) · K_t(x)) / (a - x)`
for all real `a ≠ x`.

As noted in Remark 3 of the source file, the precise value of `c` is irrelevant
for the Delsarte application because scaling `F` does not change `F(0)/F_0`.
-/
theorem cd_identity (n t : ℕ) (ht : t + 1 ≤ n) (a x : ℝ) (hax : a ≠ x) :
    ∃ c : ℝ, c > 0 ∧
      cdKernel n t a x = c *
        ((krawtchoukPoly n t).eval a * (krawtchoukPoly n (t + 1)).eval x -
         (krawtchoukPoly n (t + 1)).eval a * (krawtchoukPoly n t).eval x) /
        (a - x) := by
  refine' ⟨ ( t + 1 ) / ( 2 * Nat.choose n t ), div_pos ( by positivity ) ( mul_pos two_pos <| Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ), _ ⟩;
  induction' t with t ih;
  · simp +decide [ cdKernel, krawtchoukPoly ];
    rw [ eq_div_iff ( sub_ne_zero_of_ne hax ) ] ; ring;
  · rw [ show cdKernel n ( t + 1 ) a x = cdKernel n t a x + ( krawtchoukPoly n ( t + 1 ) |> Polynomial.eval a ) * ( krawtchoukPoly n ( t + 1 ) |> Polynomial.eval x ) / ( Nat.choose n ( t + 1 ) : ℝ ) from ?_ ];
    · rw [ ih ( by linarith ) ];
      rw [ show krawtchoukPoly n ( t + 2 ) = ( ( Polynomial.C ( n : ℝ ) - 2 * Polynomial.X ) * krawtchoukPoly n ( t + 1 ) - Polynomial.C ( ( n : ℝ ) - ↑t ) * krawtchoukPoly n t ) * Polynomial.C ( ( ( t + 2 : ℕ ) : ℝ ) ⁻¹ ) from rfl ] ; norm_num ; ring;
      rw [ show ( n.choose ( 1 + t ) : ℝ ) = ( n.choose t : ℝ ) * ( n - t ) / ( 1 + t ) from ?_ ];
      · field_simp;
        rw [ div_add_div, div_mul_eq_mul_div, div_div ];
        · ring;
        · exact sub_ne_zero_of_ne hax;
        · exact sub_ne_zero_of_ne ( by norm_cast; linarith );
      · rw [ eq_div_iff ] <;> norm_cast;
        · rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast;
          rw [ add_comm, Nat.choose_succ_right_eq, mul_comm ];
        · linarith;
    · unfold cdKernel; simp +decide [ Finset.sum_range_succ ] ;

/-- **Proposition 2, part (a) (positivity of Krawtchouk coefficients)** from the
source file.
Fix `t < n`. If `a` is strictly less than the *smallest* real zero of `K_t^{(n)}`,
then `K_j(a) > 0` for all `0 ≤ j ≤ t`. Hence the Krawtchouk coefficients of
`Φ_{n,t}(a,·)` are all nonneg, and the coefficient of `K_0` is exactly 1.

The proof uses interlacing: the smallest zero of `K_t` is less than the smallest
zero of `K_j` for `j ≤ t`, so `a` lies to the left of all zeros of every `K_j`.
Since `K_j(0) = C(n,j) > 0`, `K_j(a) > 0`.

**Note:** The source file says "largest zero" in Proposition 2(a), but the correct
condition for positivity is that `a` is below the *smallest* zero. The asymptotic
`ξ_t^{(n)}/n → 1/2 - √(τ(1-τ))` also describes the smallest zero (which is in
`[0, n/2]`), not the largest. -/
theorem krawtchouk_positive_below_smallest_zero (n t : ℕ) (ht : t + 1 ≤ n) (a : ℝ)
    (ha : ∀ ξ : ℝ, (krawtchoukPoly n t).eval ξ = 0 → a < ξ) :
    ∀ j : ℕ, j ≤ t → (krawtchoukPoly n j).eval a > 0 := by
  sorry

/-- **Proposition 2, part (b) (nonpositivity of the kernel)** from the source file.
Under the same hypotheses as part (a), there exists a threshold `η` such that
`Φ_{n,t}(a,x) ≤ 0` for every integer `x ≥ η` with `x ≤ n`.

The proof uses the CD identity: up to a positive scalar, `Φ_{n,t}(a,x)` is
`Q(x)/(a-x)` where `Q = K_t(a)·K_{t+1} - K_{t+1}(a)·K_t`. The interlacing
theorem for adjacent orthogonal polynomials controls the sign of `Q` beyond its
largest zero. -/
theorem cdKernel_nonpos_beyond_threshold (n t : ℕ) (ht : t + 1 ≤ n) (a : ℝ)
    (ha : ∀ ξ : ℝ, (krawtchoukPoly n t).eval ξ = 0 → a < ξ) :
    ∃ η : ℝ, ∀ x : ℕ, x ≤ n → η ≤ (x : ℝ) → cdKernel n t a (x : ℝ) ≤ 0 := by
  sorry

/-
**Corollary of Proposition 2 / finite-n MRRW bound** (stated in Section 7
"Optional stronger finite-n target" of the source file).
For each `n` and `t < n`, if `a < ξ_t^{(n)}` and `d > η_{n,t}(a)` (so that
`Φ_{n,t}(a,x) ≤ 0` for all `x ∈ {d,...,n}`), then `A(n,d) ≤ Φ_{n,t}(a,0)`.

This is the actual finite-n inequality from which the asymptotic MRRW bound is
extracted.
-/
theorem finite_n_mrrw_bound (n t d : ℕ) (ht : t + 1 ≤ n) (a : ℝ)
    (ha : ∀ ξ : ℝ, (krawtchoukPoly n t).eval ξ = 0 → a < ξ)
    (hd : ∀ x : ℕ, d ≤ x → x ≤ n → cdKernel n t a (x : ℝ) ≤ 0) :
    (codeA n d : ℝ) ≤ cdKernel n t a 0 := by
  convert delsarte_lp_bound n d ( fun j => if j ≤ t then ( krawtchoukPoly n j |> Polynomial.eval a ) / ( Nat.choose n j : ℝ ) else 0 ) _ _ _ using 1 <;> norm_num;
  · rw [ Finset.sum_ite ] ; norm_num [ Finset.sum_range_succ', krawtchoukPoly ];
    refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp_all +decide [ Finset.mem_range, Finset.mem_filter ];
    · exact fun x hx => le_trans hx ht.le;
    · intro j hj; rw [ mul_div_right_comm ] ; rw [ ← krawtchoukPoly_eval_nat ] ;
      · norm_num;
      · linarith;
      · grind +qlia;
  · erw [ Polynomial.eval_one ] ; norm_num;
  · intro j hj₁ hj₂; split_ifs <;> norm_num;
    exact div_nonneg ( le_of_lt ( krawtchouk_positive_below_smallest_zero n t ht a ha j ‹_› ) ) ( Nat.cast_nonneg _ );
  · intro x hx₁ hx₂; convert hd x hx₁ hx₂ using 1; simp +decide [ Finset.sum_ite, cdKernel ] ;
    refine' Finset.sum_bij ( fun j hj => j ) _ _ _ _ <;> simp_all +decide [ div_mul_eq_mul_div ];
    · exact fun b hb => le_trans hb ht.le;
    · intro j hj₁ hj₂; rw [ krawtchoukPoly_eval_nat n j x hj₁ ( by linarith ) ] ;

/-! ## Section 5: Asymptotic choice of parameters

Corresponds to Section 4 of the source file, which establishes the asymptotic
location of the largest zero of Krawtchouk polynomials (Proposition 3) and the
entropy growth rate of the objective function (Proposition 4).
-/

/-- **Proposition 3 (smallest-zero asymptotic for Krawtchouk)** from the source file.
Let `t = t_n` satisfy `t_n/n → τ ∈ [0,1/2]`. Then the *smallest* zero `ζ_t^{(n)}`
of `K_t^{(n)}` satisfies `ζ_t^{(n)}/n → 1/2 - √(τ(1-τ))`.

**Note:** The source file calls this the "largest zero," but the limit
`1/2 - √(τ(1-τ)) ∈ [0, 1/2]` is below `n/2` (the zero of `K_1`), which by
interlacing must be the *smallest* zero of `K_t`. The *largest* zero converges to
`1/2 + √(τ(1-τ))` by the symmetry `K_j(n-x) = (-1)^j K_j(x)`.

Moreover, one can choose parameters `a_n` below all zeros of `K_{t_n}^{(n)}` such
that `a_n/n` converges to `1/2 - √(τ(1-τ))` and the CD kernel is nonpositive
on the relevant range.

This is identified in Remark 4 as the only genuinely asymptotic
orthogonal-polynomial input needed for the MRRW bound. -/
theorem smallest_zero_asymptotic (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2)
    (t : ℕ → ℕ)
    (ht : Filter.Tendsto (fun n => (t n : ℝ) / (n : ℝ)) Filter.atTop (nhds τ)) :
    ∃ (a : ℕ → ℝ),
      (∀ᶠ (n : ℕ) in Filter.atTop,
        ∀ ξ : ℝ, (krawtchoukPoly n (t n)).eval ξ = 0 → a n < ξ) ∧
      Filter.Tendsto (fun n => a n / (n : ℝ)) Filter.atTop
        (nhds (1 / 2 - Real.sqrt (τ * (1 - τ)))) ∧
      (∀ᶠ (n : ℕ) in Filter.atTop, ∀ x : ℕ,
        ⌊(1 / 2 - Real.sqrt (τ * (1 - τ))) * ↑n⌋₊ ≤ x → x ≤ n →
          cdKernel n (t n) (a n) (x : ℝ) ≤ 0) := by
  sorry

/-- **Proposition 4 (entropy growth of the objective)** from the source file.
Under the same hypotheses as Proposition 3,
  `limsup_{n→∞} (1/n) · log₂ Φ_{n,t_n}(a_n, 0) ≤ H(τ)`.

The proof sketch uses the CD identity at `x = 0` together with `K_j(0) = C(n,j)`,
then compares the result to `∑_{j ≤ t_n} C(n,j)`, which grows as `2^{nH(τ) + o(n)}`
by Stirling's formula. -/
theorem entropy_growth_of_objective (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2)
    (t : ℕ → ℕ) (a : ℕ → ℝ)
    (ht : Filter.Tendsto (fun n => (t n : ℝ) / (n : ℝ)) Filter.atTop (nhds τ))
    (ha_bound : ∀ᶠ (n : ℕ) in Filter.atTop,
      ∀ ξ : ℝ, (krawtchoukPoly n (t n)).eval ξ = 0 → a n < ξ) :
    Filter.limsup (fun (n : ℕ) =>
      Real.logb 2 (cdKernel n (t n) (a n) 0) / (n : ℝ))
      Filter.atTop ≤ binaryEntropy τ := by
  sorry

/-- **Entropy asymptotic for binomial tails** (item (ii) in the proof sketch of
Proposition 4 from the source file).
For `τ ∈ [0, 1/2]`,
  `∑_{j=0}^{⌊τn⌋} C(n,j) = 2^{nH(τ) + o(n)}`,
formalized as convergence of `(1/n) · log₂(∑_{j ≤ ⌊τn⌋} C(n,j))` to `H(τ)`. -/
theorem binomial_tail_entropy_asymptotic (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) :
    Filter.Tendsto
      (fun (n : ℕ) => Real.logb 2
        (∑ j ∈ Finset.range (⌊τ * ↑n⌋₊ + 1), (Nat.choose n j : ℝ)) / (n : ℝ))
      Filter.atTop (nhds (binaryEntropy τ)) := by
  sorry

/-! ## Section 6: Conclusion of the MRRW bound

Corresponds to Section 5 of the source file, which assembles all pieces to
prove the main theorem.
-/

/-
**Involution between δ and τ** (used in the proof of Theorem 1, Section 5 of
the source file).
The map `δ ↦ τ = 1/2 - √(δ(1-δ))` is an involution on `[0, 1/2]`:
if `τ = 1/2 - √(δ(1-δ))`, then `δ = 1/2 - √(τ(1-τ))`.

This follows because `τ(1-τ) = (1/4) - δ(1-δ) = (δ - 1/2)²`,
so `√(τ(1-τ)) = 1/2 - δ` (for `δ ≤ 1/2`).
-/
theorem delta_tau_involution (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    let τ := 1 / 2 - Real.sqrt (δ * (1 - δ))
    δ = 1 / 2 - Real.sqrt (τ * (1 - τ)) := by
  ring_nf;
  rw [ Real.sq_sqrt ( by nlinarith ) ] ; rw [ eq_sub_iff_add_eq ] ; rw [ ← eq_sub_iff_add_eq' ] ; rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith

/-
`H(0) = 0`. This follows from the convention `0 · log₂ 0 = 0`, since
`Real.logb 2 0 = 0` and `Real.logb 2 1 = 0`.
-/
theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  unfold binaryEntropy; norm_num;

/-
`H(1/2) = 1`. Since `log₂(1/2) = -1`, we get
`H(1/2) = -(1/2)·(-1) - (1/2)·(-1) = 1`.
-/
theorem binaryEntropy_half : binaryEntropy (1 / 2) = 1 := by
  unfold binaryEntropy; norm_num;
  norm_num [ Real.logb_div ]

/-
**Theorem 1 (binary first MRRW bound)** from the source file.
For every `δ ∈ [0, 1/2]`,
  `R(δ) ≤ H(1/2 - √(δ(1-δ)))`.

The proof follows the assembly in Section 5 of the source file:
1. Set `τ = 1/2 - √(δ(1-δ))` (involution with `δ = 1/2 - √(τ(1-τ))`).
2. Choose `t_n` with `t_n/n → τ`.
3. By Proposition 3, choose `a_n < ξ_{t_n}` with the right asymptotic.
4. For large `n`, `⌊δn⌋ > η`, so `A(n,⌊δn⌋) ≤ Φ(a_n, 0)` by the finite-n bound.
5. By Proposition 4, `limsup (1/n) log₂ Φ(a_n,0) ≤ H(τ)`.
6. Therefore `R(δ) = limsup (1/n) log₂ A(n,⌊δn⌋) ≤ H(τ) = H(1/2 - √(δ(1-δ)))`.
-/
theorem mrrw_bound (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    rate δ ≤ binaryEntropy (1 / 2 - Real.sqrt (δ * (1 - δ))) := by
  sorry

end
