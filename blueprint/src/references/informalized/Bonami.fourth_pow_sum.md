<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: fourth_pow_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Sum of fourth powers of a sum and a difference

**Claim.** For all real `a b`,

```
(a + b) ^ 4 + (a - b) ^ 4 = 2 * (a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4)
```

The odd-degree cross terms of the two binomial expansions cancel, leaving twice
the even part.

**Proof.** A one-liner: `by ring`.

**Remark.** This is the scalar identity behind the fourth-moment
decomposition — with `a = avgLast f x`, `b = diffLast f x` it produces the
`E[g⁴] + 6E[g²h²] + E[h⁴]` shape of `fourth_moment_decomp`.

**Note.** Dead declaration: `fourth_moment_decomp` performs the same expansion
inline with `ring_nf`, so nothing in the library calls this lemma.
