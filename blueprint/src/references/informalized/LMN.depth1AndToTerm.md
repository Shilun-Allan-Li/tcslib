<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth1AndToTerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A depth-≤-1 AND subcircuit as a term

**Definition.** `depth1AndToTerm (c : Circuit n) : Term n` reads a shallow
subcircuit as one conjunction of literals:

- `c = .lit l` ↦ the one-literal term `[l.toLiteral]`;
- `c = .node _ cs` ↦ `cs.filterMap` keeping `.lit l ↦ some l.toLiteral` and
  discarding every non-literal child.

`Lit.toLiteral ⟨idx, sign⟩ = ⟨idx, !sign⟩` converts the circuit-side literal to
the switching-lemma `Literal`, whose second field is a negation flag rather than
a sign.

**Remark.** The `isAnd` flag of the node is ignored, and non-literal children are
silently dropped, so the definition is only meaningful when the node really is an
AND gate of depth ≤ 1 — precisely the situation
`depth_le_one_children_are_lits` certifies. No lemma in the file relates it to
`Circuit.eval`.

**Used in.** Nothing — `depth1AndToTerm` is dead code: no other declaration in
the repository mentions it. `depth2OrToDNF` and `depth2AndToCNF`, which handle the
same conversion, inline an equivalent `filterMap` rather than calling it.
