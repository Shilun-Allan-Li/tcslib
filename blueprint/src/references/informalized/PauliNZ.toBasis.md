<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: PauliNZ.toBasis -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Embedding the non-identity Paulis into the full Pauli basis

**Definition.** `PauliNZ` is the three-element type `{X, Y, Z}` of non-identity
single-qubit Paulis, and `PauliNZ.toBasis : PauliNZ → PauliBasis` is the obvious
inclusion into the four-element `PauliBasis = {I, X, Y, Z}`:

```
PauliNZ.X ↦ PauliBasis.X
PauliNZ.Y ↦ PauliBasis.Y
PauliNZ.Z ↦ PauliBasis.Z
```

A three-case `def` by pattern match, no proof content.

**Remark.** The point of having a separate three-element type is counting: the
Pauli strings of weight exactly `|S|` with support `S` are in bijection with
`S → PauliNZ`, whose cardinality is `3 ^ S.card`. That the map is injective is
not recorded as a lemma; it is re-derived inline in
`card_pauliStringsExactSupport` by a `rcases … <;> simp_all [PauliNZ.toBasis]`
case sweep. The one fact that *is* separated out is
`PauliNZ.toBasis_ne_I` (the image misses `I`).

**Used in.** `mkWithSupport`, `PauliNZ.toBasis_ne_I`,
`card_pauliStringsExactSupport`.
