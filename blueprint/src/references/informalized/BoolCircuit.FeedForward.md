<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: FeedForward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Layered feedforward circuits

**Definition.** `FeedForward α inp out` is a structure with five fields describing a
circuit over the value type `α`, with input nodes indexed by `inp` and output nodes by
`out`:

* `depth : ℕ` — the number of gate layers;
* `nodes : Fin (depth + 1) → Type` — the node type of each layer, layer `0` being the
  input layer and layer `depth` the output layer;
* `gates : (d : Fin depth) → nodes d.succ → Gate α (nodes d.castSucc)` — every node of
  layer `d + 1` carries a gate whose inputs are wired to nodes of layer `d`;
* `nodes_zero : nodes 0 = inp`;
* `nodes_last : nodes (Fin.last depth) = out`.

The last two are equations between types, and `attribute [simp]` is declared for both.
Since a gate at layer `d + 1` may only read layer `d`, acyclicity and the layering are
enforced by the type of `gates` rather than by a side condition; a node's value may be
read by many downstream gates, so this is a DAG, not a tree.

**Remark.** The two type-level equations are used via transport (`▸` / `Eq.rec`) rather
than by definitional unfolding, which is why the evaluation definitions in this file are
written with explicit rewrites along `nodes_zero` and `nodes_last`.

**Used in.** Everything else in this file, and the whole Razborov–Smolensky development,
which works with `FeedForward (Fin 2) (Fin n) out`.
