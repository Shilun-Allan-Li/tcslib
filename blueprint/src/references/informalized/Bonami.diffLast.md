<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: diffLast -->
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

**Used in.** `restrictLast_false_eq`, `restrictLast_true_eq`,
`fourierCoeff_diffLast`, `degree_diffLast`, and the fourth-moment / noise-operator
decompositions driving the Bonami induction in `Bonami.lean` and
`TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean`.
