<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: expect_succ_eq_iterated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Expectation on the (n+1)-cube as an iterated expectation

**Claim.** For `h : BooleanFunc (n + 1)`,

`expect h = expect (fun x' => (1/2) * (h (Fin.snoc x' false) + h (Fin.snoc x' true)))`.

Averaging over the `(n+1)`-cube is the same as averaging over the first `n`
coordinates the average of the two values obtained by appending `false` or
`true` as the last coordinate. This is Fubini for the uniform measure on
`BoolCube`.

**Proof.**

1. `unfold expect` on both sides, exposing `uniformWeight k * ∑ …`.
2. `rw [sum_boolCube_succ]` (from `Hypercontractivity/Bonami.lean`) splits
   `∑ x : BoolCube (n+1)` into `∑ x' : BoolCube n` of the two `Fin.snoc`
   extensions.
3. `norm_num [uniformWeight_succ, Finset.mul_sum, mul_add, Finset.sum_add_distrib]`
   plus `ring_nf` matches the constants: `uniformWeight (n+1) = uniformWeight n / 2`
   supplies the factor `1/2`.

**Used in.** `norm_collapse_rpow`, which specialises it to `h = fun x => |f x| ^ p`
to collapse an `Lᵖ` norm on the `(n+1)`-cube into an `n`-dimensional expectation.
