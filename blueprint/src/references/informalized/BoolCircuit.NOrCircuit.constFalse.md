<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NOrCircuit.constFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The constant-false OR-circuit

**Definition.** `NOrCircuit.constFalse : NOrCircuit n` is the base clause with
an empty literal list, the `Nodup` side condition discharged by
`List.nodup_nil`:

```
NOrCircuit.constFalse = NOrCircuit.clause [] List.nodup_nil
```

Since `NOrCircuit.eval` on a clause folds `||` over the literals starting from
`false`, this circuit evaluates to `false` on every input — the empty
disjunction. Its `NOrCircuit.depth` is `0`, its `NOrCircuit.litCount` is `0`,
and its `NOrCircuit.size` is `1`.

**Remark.** This is one of the "useful derived API" constructors in Section 7 of
`Circuit.lean`, dual to `NAndCircuit.constTrue` (the empty conjunction). It is
currently a convenience constructor only: no other declaration in `TCSlib`
references it.
