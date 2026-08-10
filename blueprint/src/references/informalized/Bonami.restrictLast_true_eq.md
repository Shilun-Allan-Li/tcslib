<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: restrictLast_true_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The true-restriction is the average minus the half-difference

**Claim.** For `f : BooleanFunc (n + 1)` and `x : BoolCube n`,

```
restrictLast f true x = avgLast f x - diffLast f x
```

i.e. `f (Fin.snoc x true)` equals the average of the two restrictions of `f`
along the last coordinate minus their half-difference.

**Proof.** Immediate from `simp [restrictLast, avgLast, diffLast]` followed by
`ring`: after unfolding, the goal is `b = (a + b)/2 - (a - b)/2` with
`a = f (Fin.snoc x false)` and `b = f (Fin.snoc x true)`.

**Used in.** `second_moment_decomp`, where it is applied backwards
(`rw [← restrictLast_true_eq]`) to recognise `avgLast f x - diffLast f x` as the
`true` restriction while splitting `∑_{x ∈ {0,1}^{n+1}} f x ^ 2`.
