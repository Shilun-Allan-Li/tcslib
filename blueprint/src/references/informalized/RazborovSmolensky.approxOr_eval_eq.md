<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOr_eval_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating the OR-approximator gives its value-level form

**Claim.** For every point `y : Fin vars → ZMod p`, every family
`polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)` and every seed
`S : Fin ℓ → Finset (Fin width)`,

`(approxOr p polys S).eval y = approxOr_val p (fun i ↦ (polys i).eval y) S`.

That is, evaluation commutes with the construction: approximating and then
evaluating is the same as evaluating the inputs and then approximating.

**Proof.** `unfold approxOr approxOr_val` exposes both sides as the same
expression `1 - ∏ k, (1 - (∑ i ∈ S k, ·) ^ (p - 1))`, one built in the polynomial
ring and one in `ZMod p`. Since `MvPolynomial.eval y` is a ring homomorphism it
commutes with `1`, subtraction, `Finset.prod`, `Finset.sum` and powers, so `aesop`
closes the goal from the corresponding `eval` simp lemmas.

**Remark.** This is the bridge that lets the seed-counting work happen entirely at
the value level (`count_bad_S`, `count_bad_S_or`) and then be lifted back to
statements about polynomials.

**Used in.** `approxOr_pointwise_bad_count`, where it rewrites the polynomial-level
bad-seed filter into the value-level one accepted by `count_bad_S_or`.
