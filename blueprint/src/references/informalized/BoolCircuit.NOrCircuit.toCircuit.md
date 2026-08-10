<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NOrCircuit.toCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Forgetting normal form: OR-circuit back to a general circuit

**Definition.** `NOrCircuit.toCircuit c : Circuit n` is the forgetful map from
the alternating normal form back into unconstrained `Circuit`, defined in a
`mutual` block with `NAndCircuit.toCircuit`:

- `.clause lits _ ↦ .node false (lits.map fun l => .lit l)` — the clause becomes
  an explicit OR gate over one literal leaf per element of `lits`; the `Nodup`
  proof is discarded.
- `.node cs ↦ .node false (cs.map NAndCircuit.toCircuit)` — an OR gate keeps its
  gate flag `false`, its children mapped by the dual function.

A plain definition; no proof. Exchanging `false`/`true` and `NOr`/`NAnd`
gives `NAndCircuit.toCircuit` verbatim.

**Remark.** The map discards two things: the `Nodup` witness on clauses, and the
guarantee of alternation. It also changes the size measure — a clause costs `1`
under `NOrCircuit.size` but becomes `1 + lits.length` nodes under
`Circuit.size`.

**Note.** Neither `NOrCircuit.toCircuit` nor `NAndCircuit.toCircuit` is
referenced outside its own `mutual` block: no companion theorem relates
`(c.toCircuit).eval` to `c.eval`, so the semantic faithfulness of the coercion
(which does hold — both cases fold `||` from `false`) is not recorded in Lean.
Currently dead code, provided as API alongside the `Circuit.toNAnd` /
`Circuit.toNOr` direction, which *is* accompanied by eval, litCount, and size
lemmas.
