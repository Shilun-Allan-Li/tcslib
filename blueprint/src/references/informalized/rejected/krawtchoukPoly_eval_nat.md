<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: krawtchoukPoly_eval_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Krawtchouk polynomial agrees with the sum formula at integer points

**Claim.** For `n j x : ℕ` with `j ≤ n` and `x ≤ n`,
`(krawtchoukPoly n j).eval (x : ℝ) = krawtchouk n j x`. That is, the polynomial
`krawtchoukPoly n j` defined by the three-term recurrence and the explicit sum
`krawtchouk n j x = ∑_{i ≤ j} (-1)^i * C(x,i) * C(n-x, j-i)` are the same
function on `{0,…,n}`, so the two presentations may be used interchangeably.

**Proof.** Strong induction on `j`, generalizing `x`
(`induction' j using Nat.strong_induction_on with j ih generalizing x`), then
`rcases j with (_ | _ | j)` matching the three arms of `krawtchoukPoly`, with
`simp_all +decide [krawtchoukPoly]` unfolding each.

1. `j = 0`: `krawtchoukPoly n 0 = 1` evaluates to `1`, and `krawtchouk_zero n x`
   gives `krawtchouk n 0 x = 1` (used symmetrically, `.symm`).
2. `j = 1`: `krawtchoukPoly n 1 = C n - 2 * X` evaluates to `n - 2x`, matched by
   `krawtchouk_one n x hx`.
3. `j + 2`: the definition supplies
   `(j+2) · K_{j+2} = (n - 2X) · K_{j+1} - C (n - j) · K_j` (as polynomials),
   and `krawtchouk_recurrence n (j+1) x` supplies the same identity for the sum
   formula at index `j+1`; the two induction hypotheses `ih` rewrite the
   evaluations of `K_{j+1}` and `K_j`. With `hj2 : (0:ℝ) < j + 2` from
   `positivity` licensing the division by `(j+2)`, `grind` closes the goal.

**Used in.** `finite_n_mrrw_bound`, twice: to convert the `krawtchoukPoly`-valued
Christoffel–Darboux kernel `cdKernel` into the `krawtchouk`-valued coefficient
family required by `delsarte_lp_bound`, both at `x = 0` and at general `x ≤ n`.
