<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: noise_qth_moment_decomp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# q-th moment decomposition for the noise operator

**Claim.** For `q : ℕ`, `ρ : ℝ` and `f : BooleanFunc (n+1)`,

`expect (fun x => (noiseOp ρ f x) ^ q) = expect (fun x' => ((noiseOp ρ (avgLast f) x' + ρ * noiseOp ρ (diffLast f) x') ^ q + (noiseOp ρ (avgLast f) x' - ρ * noiseOp ρ (diffLast f) x') ^ q) / 2)`.

The same shape as `qth_moment_decomp`, but with `T_ρ f` in place of `f`: the
`n`-cube pieces are `T_ρ (avgLast f)` and `ρ · T_ρ (diffLast f)` — the extra `ρ`
being the whole point of the lemma.

**Proof.** Reduce to `qth_moment_decomp` applied to `noiseOp ρ f`, then identify
the two pieces.

1. `convert qth_moment_decomp q (noiseOp ρ f) using 3` leaves the goal of
   matching `avgLast (noiseOp ρ f)` and `diffLast (noiseOp ρ f)` with the
   claimed pieces.
2. `avgLast (noiseOp ρ f) = noiseOp ρ (avgLast f)`: pointwise `funext`, unfold
   `avgLast`/`noiseOp`/`restrictLast` and rewrite both evaluations with
   `noiseOp_snoc`; the `boolToSign` factors are `+1` and `−1`, so the `diffLast`
   contributions cancel in the average (`ring!`).
3. `diffLast (noiseOp ρ f) = ρ • noiseOp ρ (diffLast f)`: same two `noiseOp_snoc`
   rewrites, but now the `avgLast` contributions cancel in the difference and the
   surviving factor is `ρ`. `norm_num [Algebra.smul_def]` converts the scalar
   action into multiplication so the statement matches. ∎

**Used in.** `hypercontractivity_2_2k`, where combining this with the binomial
expansion of `(A ± ρB)^{2k}` yields the sum over `j` of
`C(2k, 2j) ρ^{2j} 𝔼[A^{2k−2j} B^{2j}]`.
