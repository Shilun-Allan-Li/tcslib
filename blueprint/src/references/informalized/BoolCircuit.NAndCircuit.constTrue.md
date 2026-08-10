<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit.constTrue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The constant-true AND-circuit

**Definition.** `NAndCircuit.constTrue : NAndCircuit n` is the empty clause
`.clause [] List.nodup_nil` — an AND over no literals. The `Nodup` side
condition on the empty index list is `List.nodup_nil`.

**Remark.** By `NAndCircuit.eval` on `.clause`, the empty conjunction folds to
the unit `true`, so it evaluates to `true` on every assignment; the dual
`NOrCircuit.constFalse` is the empty disjunction and evaluates to `false`. Both
have `litCount = 0`, `size = 1`, and `depth = 0`, so they are the minimal
inhabitants of their types — which also witnesses that `NAndCircuit n` and
`NOrCircuit n` are nonempty for every `n`, including `n = 0`.

**Note.** Convenience API only: neither constant is referenced elsewhere in the
library, and no `eval` lemma is proved for either.
