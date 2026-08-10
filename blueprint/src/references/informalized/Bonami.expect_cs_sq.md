<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: expect_cs_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cauchy–Schwarz for the cross fourth moment

**Claim.** For `g h : BooleanFunc n`,
`expect (fun x => g x ^ 2 * h x ^ 2) ^ 2 ≤ expect (fun x => g x ^ 4) * expect (fun x => h x ^ 4)`.
That is, `𝔼[g²h²]² ≤ 𝔼[g⁴] · 𝔼[h⁴]` under the uniform measure on `{0,1}ⁿ`.

**Proof.**

1. `norm_num [expect]` replaces every expectation by `uniformWeight n * ∑ …`.
2. `have h_cauchy_schwarz` for raw sums:
   `(∑ x, g x ^ 2 * h x ^ 2) ^ 2 ≤ (∑ x, g x ^ 4) * (∑ x, h x ^ 4)`. This is
   `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v` applied with `u = g²`,
   `v = h²`, matched up by `convert … using 3 <;> ring`.
3. Both sides carry the same factor `uniformWeight n ^ 2`, so
   `nlinarith [show 0 ≤ uniformWeight n ^ 2 by positivity]` transfers the sum
   inequality to expectations. ∎

**Used in.** `bonami_expect` (`hCS`, bounding the cross term `C² ≤ A·B` fed to
`bonami_algebra`) and `Hypercontractivity/Simple.lean` for the noise-operator
version.
