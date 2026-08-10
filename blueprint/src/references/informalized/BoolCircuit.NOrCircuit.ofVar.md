<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NOrCircuit.ofVar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The single-variable OR-circuit

**Definition.** For `i : Fin n`, `NOrCircuit.ofVar i : NOrCircuit n` is the base
clause containing the single positive literal on variable `i`, with the `Nodup`
side condition discharged by `List.nodup_singleton`:

```
NOrCircuit.ofVar i = NOrCircuit.clause [⟨i, true⟩] (List.nodup_singleton _)
```

Here `⟨i, true⟩ : Lit n` is the literal with `idx = i` and `sign = true`, i.e.
the un-negated variable `xᵢ`. Evaluating gives `xᵢ || false = xᵢ`, so
`ofVar i` computes the projection onto coordinate `i`; its depth is `0` and its
literal count is `1`.

**Remark.** Dual to `NAndCircuit.ofVar`, which is the same one-literal clause on
the AND side. Both are convenience constructors in the derived API; nothing else
in `TCSlib` currently references the OR version.
