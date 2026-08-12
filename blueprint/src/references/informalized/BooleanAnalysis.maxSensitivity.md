<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: maxSensitivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Maximum sensitivity of a function

**Definition.** For `f : BooleanFunc n`,

```
maxSensitivity f = Finset.univ.sup (sensitivity f)
```

the largest value of `sensitivity f x` over all inputs `x : BoolCube n` — the
usual sensitivity `s(f)` of a Boolean function. A plain `noncomputable def`
with no proof content.

**Remark.** Taken as a `Finset.sup` in `ℕ`, where the empty supremum is `⊥ = 0`;
the cube `BoolCube n` is never empty (it has `2ⁿ` points, `2⁰ = 1` when
`n = 0`), so the supremum is always attained and the `⊥` branch is unreachable.

**Used in.** Nothing — no other declaration in the repository references it.
Together with `sensitivity` it forms a leaf of the development: the classical
comparisons one would expect here (`Inf_i[f] ≤ s(f)`, `I[f] ≤ s(f)`, or the
sensitivity–block-sensitivity gap) are not formalized.
