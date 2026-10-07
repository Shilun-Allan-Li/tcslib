<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: bitify_boolVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `bitify` inverts the bit-to-field cast

**Claim.** For every `b : Fin 2`,

`bitify (p := p) (boolVal (p := p) b) = b`.

So on values that came from a bit, the booleanization `bitify` recovers the
original bit exactly.

**Proof.** Immediate from `fin_cases b <;> simp [bitify, boolVal]`: for `b = 0`
the cast is `0 ≠ 1` so `bitify` returns `0`, and for `b = 1` the cast is `1` so
`bitify` returns `1`.

**Remark.** `bitify` is only well behaved on `{0, 1}`; this lemma is the precise
sense in which it is a one-sided inverse. Its companion in the other direction is
`cast_bitify_eq`, which needs the membership hypothesis explicitly.

**Used in.** `stepLayerFamily`, in the step (`hargs`) that rewrites the gate's
`bitify`-ed arguments into the actual Boolean values of the predecessor nodes, so
that `evalNode_succ_eq` can identify the gate output with the circuit value.
