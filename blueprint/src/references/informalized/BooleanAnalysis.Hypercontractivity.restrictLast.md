<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean :: restrictLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restriction of a Boolean function in its last coordinate

**Definition.** For `f : BooleanFunc (n + 1)` (that is, `(Fin (n+1) → Bool) → ℝ`)
and `b : Bool`,

```
restrictLast f b : BooleanFunc n := fun x => f (Fin.snoc x b)
```

so `restrictLast f b` is the function on the `n`-cube obtained by appending the
fixed bit `b` as the last coordinate of the input. A plain definition, marked
`noncomputable` only because `BooleanFunc` is real-valued.

**Remark.** `restrictLast f false` and `restrictLast f true` are the two
"slices" of `f`; the Bonami induction works with their average `avgLast f` and
half-difference `diffLast f` instead, via `restrictLast_false_eq` and
`restrictLast_true_eq`.

**Used in.** `BooleanAnalysis.Hypercontractivity.avgLast`, `BooleanAnalysis.Hypercontractivity.degree_avgLast`, `BooleanAnalysis.Hypercontractivity.diffLast`, `BooleanAnalysis.Hypercontractivity.expect_succ_eq`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_avgLast`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_diffLast`, `BooleanAnalysis.Hypercontractivity.fourth_moment_decomp`, `BooleanAnalysis.Hypercontractivity.restrictLast_false_eq`, `BooleanAnalysis.Hypercontractivity.restrictLast_true_eq`, `BooleanAnalysis.Hypercontractivity.second_moment_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean`; `BooleanAnalysis.Hypercontractivity.noise_qth_moment_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean`; `BooleanAnalysis.Hypercontractivity.fourth_moment_noise_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/FourthMoment.lean`; `BooleanAnalysis.Hypercontractivity.fourierCoeff_avgLast_restrictions`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_diffLast_restrictions`, `BooleanAnalysis.Hypercontractivity.noiseOp_snoc_slice` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean`; `BooleanAnalysis.Hypercontractivity.tensorize_reverse_bonami_beckner` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Tensorization.lean`.
