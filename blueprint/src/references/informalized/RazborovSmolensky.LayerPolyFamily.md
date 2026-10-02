<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: LayerPolyFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Simultaneous approximator family for one circuit layer

**Definition.** For a feed-forward circuit `F : FeedForward (Fin 2) (Fin n) out`
with finite, decidable node types, and `d ≤ F.depth`, a
`LayerPolyFamily p F ℓ d hd` bundles a seeded polynomial for *every* node of layer
`d` at once. Its fields:

- `Seed : Type`, with instance fields `seedFintype` and `seedDecEq` (made
  instances by `attribute [instance] LayerPolyFamily.seedFintype LayerPolyFamily.seedDecEq`);
- `card_pos : 0 < Fintype.card Seed`;
- `poly : Seed → F.nodes ⟨d, _⟩ → MvPolynomial (Fin n) (ZMod p)`;
- `degree : ∀ s u, (poly s u).totalDegree ≤ circuitDegreeBound p ℓ d`;
- `bad`: for every Boolean input `x`,
  `#{s : Seed | ∃ u, (poly s u).eval (boolInput (p := p) x) ≠ ((F.evalNode u x : Nat) : ZMod p)} * 2 ^ ℓ ≤ gateCountBefore F d hd * Fintype.card Seed`.

**Remark.** Two design choices matter. First, the failure event is existential
over nodes `u`, so a seed counts as bad if it is wrong at *any* node of the layer
— which is what makes the family composable. Second, the error budget grows with
`gateCountBefore F d hd`, the number of non-input gates in the first `d` layers:
each layer contributes a union bound over its own nodes, and the accumulated count
is the union bound over the whole prefix of the circuit.

**Used in.** `inputLayerFamily` (base case, `d = 0`, seed `PUnit`, `poly = X`),
`stepLayerFamily` (inductive step, seed `A.Seed × Tail`), `buildLayerFamily`
(the recursion), and the circuit-level theorems
`exists_poly_distribution_for_circuit_outputs`, `…_one`, and
`exists_poly_list_for_circuit_one`.
