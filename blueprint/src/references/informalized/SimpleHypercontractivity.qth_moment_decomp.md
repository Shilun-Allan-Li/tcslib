<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: qth_moment_decomp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The q-th moment as an average of two last-bit restrictions

**Claim.** For `q : ℕ` and `f : BooleanFunc (n+1)`,

`expect (fun x => f x ^ q) = expect (fun x' => ((avgLast f x' + diffLast f x') ^ q + (avgLast f x' - diffLast f x') ^ q) / 2)`.

The `q`-th moment on the `(n+1)`-cube equals the `n`-cube expectation of the
average of the two restrictions' `q`-th powers, written in the `avgLast ± diffLast`
coordinates. No hypothesis on `q` is needed — this is a bookkeeping identity, not
a parity statement.

**Proof.**

1. `unfold expect` and `uniformWeight_succ` replace the weight `2⁻⁽ⁿ⁺¹⁾` by
   `uniformWeight n / 2` — this is where the division by `2` comes from.
2. `sum_boolCube_succ` splits `∑ x : BoolCube (n+1), f x ^ q` into
   `∑ x, f (Fin.snoc x false) ^ q + ∑ x, f (Fin.snoc x true) ^ q`.
3. `unfold avgLast diffLast`: by definition `avgLast f x' ± diffLast f x'` is
   exactly `f (Fin.snoc x' false)` resp. `f (Fin.snoc x' true)`, so the two sides
   agree termwise; `norm_num [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]`
   with `ring_nf` and a final `rfl` close it. ∎

**Used in.** `noise_qth_moment_decomp`, which applies it to `noiseOp ρ f` in
place of `f`.
