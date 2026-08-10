<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitReindex.lean :: Circuit.reidx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Re-indexing the gate inputs of a circuit

**Definition.** `Circuit.reidx : Circuit m → (Fin m → Fin m') → Circuit m'`
renames every variable (gate) index of a circuit along `f : Fin m → Fin m'`, by
structural recursion:

- `(.lit l).reidx f = .lit ⟨f l.idx, l.sign⟩` — the index is pushed through `f`,
  the sign is kept;
- `(.node isAnd cs).reidx f = .node isAnd (cs.map (fun c => c.reidx f))` — the
  gate type is kept and the map is applied recursively to all children.

`f` need not be injective, so re-indexing may identify distinct inputs.

**Remark.** The tree shape is untouched by construction, which is what makes the
two companion lemmas cheap: `Circuit.reidx_depth` gives
`(c.reidx f).depth = c.depth`, and `Circuit.reidx_eval` gives
`(c.reidx f).eval g = c.eval (g ∘ f)`.

**Used in.** `reidx_eval_mergeGates_left` / `reidx_eval_mergeGates_right`
(`LMN/GateMerge.lean`), where `Fin.castAdd` and `Fin.natAdd` re-point two
circuits into a merged gate array without changing what they compute.
