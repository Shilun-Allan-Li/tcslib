/-- The polynomial-over-order correction is subexponentially small at every exponent below
one when the prime schedule is at least `2^κ`. This uses the shared subexponential notion.

**Proof sketch.** Bound the correction by `4d(κ)2⁻κ`, use the polynomial growth bound for
`d`, and apply `subexpSmall_two_pow_neg`, `SubexpSmall.mul_pow`, `.const_mul` and `.mono`. -/
theorem mddhSlack_subexpSmall (p : ℕ → ℕ) (d : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) :
    SubexpSmall c (mddhSlack p d) :=
  Eq.mpr (congrArg (SubexpSmall c) (funext (mddhSlack_eq p d)))
    (mddhCorrection_subexpSmall p d hpb hc₀ hc₁)
