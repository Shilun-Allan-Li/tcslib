<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: weighted_sum_succ_decomp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The kernel-weighted bilinear sum splits off the last coordinate

**Claim.** For `ρ : ℝ` and any `F : BoolCube (n+1) → BoolCube (n+1) → ℝ`,
the kernel-weighted average
`uniformWeight (n+1) * ∑ x, ∑ y, noiseKernel ρ x y * F x y`
equals
`uniformWeight n * ∑ x', ∑ y', noiseKernel ρ x' y' * ((1/2) * ∑ b, ∑ b', ((1 + ρ * boolToSign b * boolToSign b')/2) * F (Fin.snoc x' b) (Fin.snoc y' b'))`,
where `x' y' : BoolCube n` range over the first `n` coordinates. Fubini for the
Boolean cube, specialised to the product structure of the noise kernel.

**Proof.** Entirely rewriting; no auxiliary inequality.

1. Split both cube sums along the last bit with `sum_boolCube_succ` (used twice:
   once via `congr_arg` on the outer sum, once inside `Finset.sum_congr` for the
   inner one).
2. Replace `uniformWeight (n+1)` by `uniformWeight n / 2` (`uniformWeight_succ`) and
   distribute the weight over the split sums
   (`Finset.sum_add_distrib`, `Finset.mul_sum`, `mul_add`, `ring_nf`).
3. Factor the kernel along the last coordinate: each of the four `(b, b')` terms is
   rewritten by `noiseKernel_snoc`, giving
   `noiseKernel ρ x' y' * ((1 + ρ * boolToSign b * boolToSign b')/2)`.
4. `norm_num [boolToSign]; ring` matches the two-element `Bool` sums with the
   explicit four-term expansion. ∎

**Used in.** `two_func_hyp_succ` (`h_lhs`), where the last bit is peeled off so that
the one-bit base case and the induction hypothesis can be applied separately.
