<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit.toCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Forgetting the normal-form constraints (AND side)

**Definition.** `NAndCircuit.toCircuit : NAndCircuit n → Circuit n`, defined in a
`mutual` block with `NOrCircuit.toCircuit`, is the forgetful map back into the
unconstrained circuit type:

- `.clause lits _ => .node true (lits.map fun l => .lit l)` — a clause becomes an
  AND gate whose children are the literals as leaves; the `Nodup` proof is
  dropped;
- `.node cs => .node true (cs.map NOrCircuit.toCircuit)` — an AND gate becomes an
  AND gate, with each `NOrCircuit` child translated by the dual function.

The dual `NOrCircuit.toCircuit` is identical with `false` (OR) in place of
`true`. Note the direction: this is a one-way coercion, not an inverse of
`Circuit.toNAnd`, and it is not injective on the nose — the `Nodup` witness and
the clause-versus-gate distinction are both erased, so a clause and a
same-shaped gate over singleton clauses have the same image.

**Used in.** Section 6 of the file ("Coercion: NCircuit → Circuit"), which lets
statements proved about `Circuit` (evaluation, `size`, `depth`, `maxFanin`) be
transported to normal-form circuits without duplicating the API.
