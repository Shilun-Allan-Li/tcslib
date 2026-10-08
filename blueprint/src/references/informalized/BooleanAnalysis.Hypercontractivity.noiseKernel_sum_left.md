<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Duality.lean :: noiseKernel_sum_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The noise kernel sums to one over its first argument

**Claim.** For `0 ≤ ρ ≤ 1` and any `y : BoolCube n`,
`∑ x : BoolCube n, noiseKernel ρ x y = 1`. Together with
`noiseKernel_sum_right` this says the kernel is doubly stochastic.

**Proof.** Immediate from the symmetry of the kernel in its two arguments:
`convert noiseKernel_sum_right hρ0 hρ1 y using 1`, then `unfold noiseKernel` and
match the two products coordinatewise (`congr; ext; ring_nf; ac_rfl`) — the
factor `(1 + ρ · boolToSign (x i) · boolToSign (y i))/2` is unchanged by
swapping `x` and `y`.

**Used in.** `BooleanAnalysis.Hypercontractivity.trivial_contractivity` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Duality.lean`; `BooleanAnalysis.Hypercontractivity.lpMean_noise_antitone` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Tensorization.lean`.
