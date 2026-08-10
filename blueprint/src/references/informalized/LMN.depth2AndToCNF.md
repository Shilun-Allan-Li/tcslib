<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth2AndToCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An AND-top depth-≤-2 circuit as a CNF

**Definition.** `depth2AndToCNF (cs : List (Circuit n)) : CNF n` is
`cs.flatMap` of the per-child contribution, where the top gate is understood to
be an AND over `cs`:

- `.lit l` ↦ `[[l.toLiteral]]`, the unit clause;
- `.node false cs'` (an OR child) ↦ one clause, the literals of `cs'` collected
  by `filterMap`;
- `.node true cs'` (an AND child) ↦ one unit clause per literal of `cs'`, since
  an AND inside an AND flattens.

Non-literal grandchildren are dropped by the `filterMap`, so the translation is
faithful only when every child has depth ≤ 1 — guaranteed in use by
`depth_le_two_children_depth_le_one` and `depth_le_one_children_are_lits`.
`Lit.toLiteral` flips the sign convention (`neg = !sign`).

Two lemmas justify it, both taking `(Circuit.node true cs).depth ≤ 2`:

- `depth2AndToCNF_eval` — `CNF.eval (depth2AndToCNF cs) x = (Circuit.node true cs).eval x`;
- `depth2AndToCNF_width_le` — `CNF.width (depth2AndToCNF cs) ≤ (Circuit.node true cs).maxFanin`.

**Remark.** `depth2OrToDNF` is the exact dual, with the roles of the `isAnd` flags
`true`/`false` exchanged.

**Used in.** `depth2_circuit_switching_bound` in
`LMN/CircuitLayerReduction.lean`: in the AND-top case it rewrites the circuit's
evaluation into this CNF and applies
`switching_bernoulli_dtDepth_cnf_general`.
