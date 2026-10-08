<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean :: restrictLast_true_eq -->
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

**Used in.** `BooleanAnalysis.Hypercontractivity.second_moment_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean`.
