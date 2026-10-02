<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: gateCountBefore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Number of non-input gates in the first `d` layers

**Definition.** For a Boolean feedforward circuit `F : FeedForward (Fin 2) (Fin n) out`
with every layer finite (`[∀ i, Fintype (F.nodes i)]`),
`gateCountBefore F : (d : ℕ) → d ≤ F.depth → ℕ` is defined by recursion on `d`:

- `gateCountBefore F 0 _ = 0`;
- `gateCountBefore F (d + 1) hd = gateCountBefore F d _ + Fintype.card (F.nodes ⟨d + 1, _⟩)`.

So it is `∑_{i = 1}^{d} |F.nodes i|` — layer `0`, the input layer, contributes
nothing, matching the reading "non-input gates".

Notes on the Lean form:

- The proof argument `hd : d ≤ F.depth` is not decoration: it is what lets the
  index `⟨d + 1, _⟩` be built as a `Fin (F.depth + 1)`, so the count is a
  function of both `d` and its bound. Callers must therefore pass a proof, and
  two calls at the same `d` agree by proof irrelevance.
- Marked `noncomputable`: the `Fintype` instances come from the ambient
  instance argument, not from data.

**Used in.** The error term of every `LayerPolyFamily` bad-seed bound, and hence
in `gateCountBefore_zero`, `gateCountBefore_succ`, `inputLayerFamily`,
`stepLayerFamily`, and the three `exists_poly_*_for_circuit_*` theorems, where
`gateCountBefore F F.depth _` is the total gate count charged against the
failure probability.
