<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean :: diffLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Half-difference of a Boolean function in its last coordinate

**Definition.** For `f : BooleanFunc (n + 1)`,

```
diffLast f : BooleanFunc n := fun x => (restrictLast f false x - restrictLast f true x) / 2
```

i.e. half the difference of the two slices `f (Fin.snoc x false)` and
`f (Fin.snoc x true)`. A plain definition (`noncomputable`, like
`restrictLast`), the companion of `avgLast f`, which uses `+` in place of `-`.

**Remark.** `avgLast` and `diffLast` split `f` along its last coordinate:
`restrictLast_false_eq` and `restrictLast_true_eq` recover the slices as
`avgLast f ± diffLast f`, and `fourierCoeff_diffLast` identifies the Fourier
coefficients of `diffLast f` at `S` with those of `f` at
`S.image Fin.castSucc ∪ {Fin.last n}` — the part of the spectrum that *does*
involve the last variable.

**Used in.** `BooleanAnalysis.Hypercontractivity.bonami_expect` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Bonami.lean`; `BooleanAnalysis.Hypercontractivity.degree_diffLast`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_diffLast`, `BooleanAnalysis.Hypercontractivity.fourth_moment_decomp`, `BooleanAnalysis.Hypercontractivity.restrictLast_false_eq`, `BooleanAnalysis.Hypercontractivity.restrictLast_true_eq`, `BooleanAnalysis.Hypercontractivity.second_moment_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean`; `BooleanAnalysis.Hypercontractivity.hypercontractivity_2_2k`, `BooleanAnalysis.Hypercontractivity.noise_qth_moment_decomp`, `BooleanAnalysis.Hypercontractivity.qth_moment_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean`; `BooleanAnalysis.Hypercontractivity.fourth_moment_noise_decomp`, `BooleanAnalysis.Hypercontractivity.hypercontractivity_2_4`, `BooleanAnalysis.Hypercontractivity.noiseOp_snoc` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/FourthMoment.lean`; `BooleanAnalysis.Hypercontractivity.fourierCoeff_diffLast_restrictions`, `BooleanAnalysis.Hypercontractivity.noiseOp_snoc_slice` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean`.
