<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: second_pow_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Parallelogram identity for real squares

**Claim.** For all real `a b`,

```
(a + b) ^ 2 + (a - b) ^ 2 = 2 * (a ^ 2 + b ^ 2)
```

The `2ab` cross terms cancel.

**Proof.** A one-liner: `by ring`.

**Remark.** The scalar identity behind `second_moment_decomp`: with
`a = avgLast f x` and `b = diffLast f x` it yields
`E[f²] = E[g²] + E[h²]` once averaged over the last coordinate.

**Note.** Dead declaration: `second_moment_decomp` expands the squares inline
(`add_sq`, `sub_sq`, `ring_nf`), so nothing in the library calls this lemma.
