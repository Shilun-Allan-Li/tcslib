<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: onlyUsesGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restricting a circuit to a gate set

**Definition.** For `F : FeedForward α inp out` and a set of operations
`S : Set (GateOp α)`,

`F.onlyUsesGates S ↔ ∀ d u, (F.gates d u).op ∈ S`,

i.e. the operation of every gate — at every layer index `d : Fin F.depth` and every
node `u` of layer `d + 1` — lies in `S`. Only the `op` component is constrained; the
wiring `inputs` is unrestricted.

**Remark.** This is the "circuit class" hypothesis of the development: instantiating
`S := ACp_GateOps p` says `F` is an `AC⁰[p]` circuit, which is what licenses the
per-gate low-degree polynomial approximation.

**Used in.** `exists_poly_distribution_for_circuit_outputs_size`,
`exists_poly_distribution_for_circuit_one_size` and
`exists_poly_list_for_circuit_one_size` in `RazborovSmolensky/CircuitSize.lean`, and the
corresponding statements in `CircuitDegree.lean` / `RazborovSmolensky.lean`.
