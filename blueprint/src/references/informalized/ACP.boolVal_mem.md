<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: boolVal_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The field value of a bit is `0` or `1`

**Claim.** For every `b : Fin 2`,

`boolVal (p := p) b ∈ ({0, 1} : Set (ZMod p))`.

**Proof.** Immediate from `fin_cases b <;> simp [boolVal]`: the two cases
evaluate the cast to `0` and to `1`, and each is a member of the doubleton.

**Remark.** A granular helper, not a mathematical step. It exists because the
`bad` fields of `GatePolyFamily` and `LayerPolyFamily` take a hypothesis
`∀ i, inputs i ∈ ({0, 1} : Set (ZMod p))`, and in `stepLayerFamily` the incoming
values are exactly casts of node values, so this lemma is what discharges that
hypothesis.

**Used in.** `stepLayerFamily` (the `hbits` argument fed to `(Fam u).bad`).
