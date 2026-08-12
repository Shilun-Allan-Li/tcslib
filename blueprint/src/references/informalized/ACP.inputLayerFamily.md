<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: inputLayerFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The input layer is represented exactly by variables

**Definition.** For a Boolean feedforward circuit
`F : FeedForward (Fin 2) (Fin n) out` with finite, decidable-equality layers and
`hd : 0 ≤ F.depth`, `inputLayerFamily p F ℓ hd : LayerPolyFamily p F ℓ 0 hd` is the
base case of the layer induction: seed type `PUnit`, and for the unique seed the
node `u` of layer `0` is represented by the single variable
`MvPolynomial.X (F.nodes_zero ▸ u)`, transporting `u` along
`F.nodes_zero : F.nodes 0 = Fin n`. `noncomputable`, built by `refine` on the
structure fields after `classical`.

**Proof (of the structure's fields).**

- `card_pos` — `simp`: `Fintype.card PUnit = 1`.
- `degree` — `simp [circuitDegreeBound]`: the target is
  `circuitDegreeBound p ℓ 0 = ((p - 1) * ℓ) ^ 0 = 1`, and a variable has total
  degree `1`.
- `bad` — the bad-seed set is shown to be `∅` (`ext`, then `Finset.mem_filter`
  in one direction and `cases` on the empty membership in the other): for any
  layer-`0` node `u`, `simp [FeedForward.evalNode, boolInput]` gives
  `(X (F.nodes_zero ▸ u)).eval (boolInput p x) = ((F.evalNode u x : Fin 2) : ZMod p)`,
  since `evalNode` at layer `0` just reads the input. Then `rw` and
  `simp [gateCountBefore]` close the bound.

**Remark.** The empty bad set is not merely convenient: the right-hand side of
the bound is `gateCountBefore F 0 hd * Fintype.card Seed = 0`, so the base case
*must* be error-free.

**Used in.** `buildLayerFamily` at `d = 0`, hence in all three
`exists_poly_*_for_circuit_*` theorems.
