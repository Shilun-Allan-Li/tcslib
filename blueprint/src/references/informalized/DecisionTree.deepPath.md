<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: DecisionTree.deepPath -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Extracting a deepest root-to-leaf path

**Definition.** `DecisionTree.deepPath : DecisionTree n → List (Fin n × Bool)`
returns a deepest root-to-leaf path as the list of
`(queried variable, direction taken)` pairs along it:

- `deepPath (.leaf _) = []` — nothing is queried at a leaf;
- `deepPath (.branch v lo hi) = if hi.depth ≥ lo.depth then (v, true) :: hi.deepPath
  else (v, false) :: lo.deepPath` — record the query at `v`, then descend into
  whichever subtree is deeper, breaking ties toward `hi`.

So the choice is greedy and deterministic: at every branch it steps into a
subtree realising the `max` in `DecisionTree.depth`, which is exactly why
`DecisionTree.length_deepPath` gives `T.deepPath.length = T.depth` (proved by
induction on `T`, `split` on the same guard, then `omega`).

**Remark.** The `Bool` component is the *branch direction*, i.e. the value the
path assigns to `v` — `true` means the `hi` subtree was taken, matching the
orientation of `DecisionTree.eval`. A `deepPath` is therefore readable as a
partial assignment fixing `T.depth` coordinates.

**Used in.** The encoding argument of the switching lemma
(`Switching/Encoding.lean`, `Switching/EncodingProperties.lean`) and the
canonical decision tree (`Switching/CanonicalDTree.lean`), where turning the
abstract depth of a tree into a concrete witnessing path is what lets a
depth lower bound be contradicted.
