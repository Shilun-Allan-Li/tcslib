<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: restrictLast_false_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The false-restriction is the sum of the average and half-difference

**Claim.** For `f : BooleanFunc (n + 1)` and `x : BoolCube n`,

```
restrictLast f false x = avgLast f x + diffLast f x
```

i.e. `f (Fin.snoc x false)` equals the average of the two restrictions plus
their half-difference.

**Proof.** Immediate from `simp [restrictLast, avgLast, diffLast]` followed by
`ring`: unfolding the three definitions turns the goal into
`a = (a + b)/2 + (a - b)/2` with `a = f (Fin.snoc x false)`,
`b = f (Fin.snoc x true)`, which `ring` closes.

**Remark.** A deliberately granular helper: together with
`restrictLast_true_eq` it is the whole content of the "even/odd part"
decomposition in the last variable used by the Bonami induction.

**Note.** Unlike `restrictLast_true_eq`, this lemma currently has no callers in
the library.
