<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: exists_squarefree_representative_on_rootCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every function on `{1, ω}^n` is a squarefree polynomial, in coefficient form

**Claim.** For any field `K`, any `ω : K` and any `f : rootCube ω n → K` there is a
coefficient function `c : Finset (Fin n) → K` with
`(squarefreePolynomial c).eval x.1 = f x` for every `x` in the cube. No degree bound is
claimed — `c` ranges over all subsets.

**Proof.** `by_cases hω1 : ω = 1`.

* `ω = 1`: the cube is the single point `x0 = fun _ => 1` (each coordinate is `1` or `ω = 1`,
  by `Subtype.ext` + `funext`). Take `c s = if s = ∅ then f x0 else 0`; the evaluation is a
  sum with one surviving term by `Finset.sum_eq_single_of_mem`, and `simp [squarefreePolynomial,
  squarefreeMonomial]` identifies it with `f x0 = f x`.
* `ω ≠ 1`: two-point Lagrange interpolation in each coordinate, expanded in the squarefree
  basis. Put `a = (ω - 1)⁻¹` (so `a * (ω - 1) = 1` by `mul_inv_cancel₀`), and for each
  `s : Finset (Fin n)` set `A s i = if i ∈ s then a else -a`, `B s i = if i ∈ s then -a else a * ω`.
  Also `point s` is the cube point that is `ω` exactly on `s`, and `code x = univ.filter (x.1 · = ω)`
  its inverse (`hpoint_code`, via `Subtype.ext`).
  1. `hcoordinate`: a four-way `by_cases` on `i ∈ s` and `x.1 i = ω` shows
     `A s i * x.1 i + B s i = if (i ∈ s ↔ x.1 i = ω) then 1 else 0`; each branch is a `calc`
     ending in `ring` and `ha_mul`.
  2. `hprod_indicator`: multiplying over all `i` gives `if s = code x then 1 else 0`. The
     `0/1`-product is evaluated by `Finset.prod_eq_zero` at a failing coordinate
     (`not_forall.mp`), and `∀ i, i ∈ s ↔ x.1 i = ω` is equivalent to `s = code x`.
  3. `hinner`: `Finset.prod_add` rewrites that product as the sum over subsets `t` of
     `(∏ i ∈ t, A s i * x.1 i) * (∏ i ∈ univ \ t, B s i)`, i.e. exactly a squarefree
     expansion in `x`.
  4. Choosing `c t = ∑ s, f (point s) * (∏ i ∈ t, A s i) * (∏ i ∈ univ \ t, B s i)`,
     `heval_expand` swaps the two sums (`Finset.sum_comm`, `Finset.sum_mul`, `Finset.mul_sum`)
     so that `hinner` applies, collapsing the outer sum to the single term `s = code x` via
     `Finset.sum_eq_single_of_mem`, which is `f (point (code x)) = f x`.

**Remark.** Runs under `set_option maxHeartbeats 1000000`; the degree-controlled version is
`lowDegree_squarefree_complete_on_rootCube`.
