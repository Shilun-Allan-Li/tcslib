<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: boolInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Boolean input vector as a point of the prime field

**Definition.** For `x : Fin n → Fin 2`,

`boolInput p x = fun i => ((x i : Nat) : ZMod p)`,

the coordinatewise cast of a Boolean input into `ZMod p`. Its image lies in
`{0, 1} ⊆ ZMod p`.

**Remark.** This is the fixed evaluation point at which every polynomial in the
Razborov–Smolensky argument is compared against the circuit: statements are all
of the shape `(P s).eval (boolInput (p := p) x) ≠ ((F.eval x o : Nat) : ZMod p)`.
Having it as a named definition (rather than an inline lambda) is what lets
`dsimp [boolInput]` and `simp [boolInput]` normalize those goals uniformly.
`boolVal` is the one-bit version of the same cast.

**Used in.** The `bad` fields of `GatePolyFamily` and `LayerPolyFamily`, all of
`inputLayerFamily` / `stepLayerFamily`, the circuit-level theorems
`exists_poly_distribution_for_circuit_outputs`, `…_one`,
`exists_poly_list_for_circuit_one`, and downstream in `CircuitSize.lean`,
`SmolenskyAlgebra.lean`, and `RazborovSmolensky.lean`.
