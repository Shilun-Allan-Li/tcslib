<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: noise_l2_abs_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Passing to absolute values does not decrease the noisy L² quantity

**Claim.** For `a b ρ : ℝ` with `0 ≤ ρ ≤ 1`,

```
a ^ 2 + ρ ^ 2 * b ^ 2
  ≤ ((|a+b| + |a-b|) / 2) ^ 2 + ρ ^ 2 * ((|a+b| - |a-b|) / 2) ^ 2
```

Reading `u = a + b`, `v = a − b`, the right-hand side is the same expression
`a'² + ρ²b'²` formed from the *absolute values* `|u|, |v|` in place of `u, v`, so
replacing a one-bit function by its pointwise absolute value can only increase
`𝔼[(T_ρ f)²]` when `ρ ≤ 1`.

**Proof.** Two steps.

1. `have h_simp : (a+b) * (a-b) ≤ |a+b| * |a-b|`, by
   `cases abs_cases (a+b) <;> cases abs_cases (a-b) <;> nlinarith` — a product is
   at most the product of the absolute values.
2. `nlinarith` closes the goal from `h_simp`, the fact `0 ≤ 1 - ρ ^ 2` (from
   `ρ ≤ 1`), and `abs_mul_abs_self` for `a+b` and `a-b`; expanding both sides,
   the difference is `(1 − ρ²)/2 · (|a+b||a-b| − (a+b)(a-b))`. ∎

**Note.** `private`-free but currently **unreferenced**: the eventual
`two_point_ineq` handles the absolute values directly by a WLOG argument, so this
lemma records the intended reduction rather than being on the live path.
