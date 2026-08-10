<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: restrictLast -->
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

**Used in.** `avgLast`, `diffLast`, and throughout the last-coordinate
decomposition lemmas in `Bonami.lean` and
`TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean`.
