<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NOrCircuit.depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth of a normal-form OR-circuit

**Definition.** `NOrCircuit.depth : NOrCircuit n → Nat` counts gate levels above
the base clauses:

```
(NOrCircuit.clause lits h).depth = 0
(NOrCircuit.node cs).depth       = 1 + cs.foldr (fun c acc => max c.depth acc) 0
```

A base clause has depth `0`, and an OR-node has one more than the maximum depth
of its `NAndCircuit` children (`0` for an empty child list). It is declared in a
`mutual` block with `NAndCircuit.depth`, whose two equations are identical on
the AND side — the recursion has to alternate because `NOrCircuit.node` takes
`List (NAndCircuit n)` and vice versa.

**Remark.** The convention charges nothing for the literals inside a base
clause, so the depth-2 DNF/CNF shapes used by the switching lemma
(`NOrCircuit.node [NAndCircuit.clause …]`) have depth `1` under this measure,
not `2`. No other declaration in `TCSlib` currently references it.
