<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: buildLayerFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Building the layer families by recursion on depth

**Definition.** Given `F : FeedForward (Fin 2) (Fin n) out` with finite,
decidable node types and `hUses : F.onlyUsesGates (ACp_GateOps p)`, and given `ℓ`,

`buildLayerFamily p F hUses ℓ : (d : ℕ) → (hd : d ≤ F.depth) → LayerPolyFamily p F ℓ d hd`

is defined by structural recursion on `d`:

- `d = 0`: `inputLayerFamily (p := p) F ℓ hd` — the layer-`0` family whose
  polynomial is the variable `MvPolynomial.X` of the corresponding input node, with
  seed `PUnit` and no failures.
- `d + 1`: with `hdlt : d < F.depth := Nat.lt_of_succ_le hd`, apply
  `stepLayerFamily (p := p) F hUses ℓ d hdlt` to the recursively built
  `buildLayerFamily F hUses ℓ d (Nat.le_of_lt hdlt)`.

It is `noncomputable`, because `stepLayerFamily` reaches each gate's approximator
through `gatePolyFamily`, i.e. `Classical.choose`.

**Remark.** No proof obligations are discharged here: all the content lives in the
two constructors it composes — `inputLayerFamily` for the base case and
`stepLayerFamily` for the inductive step, which multiplies the seed by the layer's
gate seeds, multiplies the degree bound by `(p - 1) * ℓ`, and adds this layer's
node count to the error budget. The hypothesis `hUses` is threaded unchanged so
that every gate encountered lies in `ACp_GateOps p`.

**Used in.** `exists_poly_distribution_for_circuit_outputs`,
`exists_poly_distribution_for_circuit_one` (both instantiate it at
`d = F.depth` with `Nat.le_refl`), and through the latter
`exists_poly_list_for_circuit_one`.
