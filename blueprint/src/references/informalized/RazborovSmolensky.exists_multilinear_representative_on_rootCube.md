<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: exists_multilinear_representative_on_rootCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every function on `{1, ω}^n` is represented by a polynomial

**Claim.** For a field `K`, `ω : K`, and any `f : rootCube ω n → K`, there is a
polynomial `P : MvPolynomial (Fin n) K` with `P.eval x.1 = f x` for every point
`x` of the cube `rootCube ω n = {x : Fin n → K // ∀ i, x i = 1 ∨ x i = ω}`. No
degree bound is asserted, despite the name.

**Proof.** Case split on `ω = 1` (`by_cases`).

- If `ω = 1` the cube is the single point `x0 = fun _ => 1`: any `x` equals `x0`
  by `Subtype.ext`, `funext`, and `rcases x.2 i` (the `x i = ω` branch closes by
  `simpa [hω1]`). Take `P := MvPolynomial.C (f x0)`.
- If `ω ≠ 1` then `ω - 1 ≠ 0` (`sub_ne_zero.mpr`), so the two coordinate
  indicators `χω i := C (ω-1)⁻¹ * (X i - C 1)` and `χ1 i := C (ω-1)⁻¹ * (C ω - X i)`
  are the Lagrange basis on `{1, ω}`. Set
  `P := ∑ s : Finset (Fin n), C (f (point s)) * ∏ i, (if i ∈ s then χω i else χ1 i)`,
  where `point s` is the cube point with `ω` exactly on `s`, and
  `code x := univ.filter (fun i => x.1 i = ω)` is its inverse (`hpoint_code`, by
  `Subtype.ext` and a case split on `x.1 i = ω`). Then:
  1. `hfactor`: each factor evaluates to `1` or `0` according to
     `i ∈ s ↔ x.1 i = ω`, using `mul_inv_cancel₀ hωm1` in the matching cases.
  2. `hindicator`: the product is `1` iff `s = code x` — the pointwise
     equivalences combine into `s = code x` (`hEq`), and a mismatching index makes
     the product vanish by `Finset.prod_eq_zero`.
  3. `hterm_eval`: hence the `s`-th summand is `if s = code x then f x else 0`,
     using `hpoint_code` in the matching case.
  4. Summing, `simp` collapses the single surviving term (`hsum_final`) to `f x`.

**Remark.** This is ordinary two-point interpolation coordinatewise; the `ω = 1`
branch exists only because `rootCube` does not require `ω ≠ 1`.
