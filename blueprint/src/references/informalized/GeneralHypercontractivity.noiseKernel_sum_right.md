<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: noiseKernel_sum_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The noise kernel sums to one over its second argument

**Claim.** For `0 ≤ ρ ≤ 1` and any `x : BoolCube n`,
`∑ y : BoolCube n, noiseKernel ρ x y = 1`. So for each fixed `x` the kernel
`K_ρ(x, ·) = ∏ i (1 + ρ · sign(x i) · sign(y i))/2` is a probability
distribution on the cube.

**Proof.** Two steps, both mechanical.

1. `unfold noiseKernel`, then `h_factor`: the sum of a product over independent
   coordinates factors as a product of sums,
   `∑ y ∏ i (…) = ∏ i ∑ b : Bool (1 + ρ · sign(x i) · sign b)/2`, which is
   exactly `Fintype.prod_sum` (used via `Eq.symm`).
2. `Finset.prod_eq_one`: each coordinate factor is `1`, since the two Boolean
   values contribute `(1 + ρ·s)/2 + (1 − ρ·s)/2 = 1`
   (`norm_num [Finset.sum_div, boolToSign]; ring`).

**Remark.** The hypotheses `_hρ0 : 0 ≤ ρ` and `_hρ1 : ρ ≤ 1` are unused — the
identity is an algebraic one, valid for every `ρ`. They are kept so the lemma
matches the signature of its callers (see the file's header note about
`ρ`-range hypotheses).

**Used in.** `noiseKernel_sum_left` and `noiseOp_abs_rpow_le_kernel_avg` (as the
"weights sum to 1" side condition of Jensen).
