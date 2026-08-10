<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: CNF.width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width of a CNF formula

**Definition.** `CNF.width (c : CNF n) : ℕ` is the largest clause width in `c`:

```
CNF.width c = (c.map Term.width).foldr max 0
```

i.e. take each clause's width `Term.width t = t.length`, then fold `max` over
the resulting list starting from `0`. Consequences that follow directly from the
`foldr`:

- the empty formula has width `0`;
- every clause `t ∈ c` satisfies `t.length ≤ CNF.width c`;
- a formula all of whose clauses are empty also has width `0`, so `width c = 0`
  does not mean `c = []`.

**Remark.** The body is character-for-character the same as `DNF.width` — the
two are separate declarations only because `CNF n` and `DNF n` are separate
(definitionally equal) abbreviations for `List (Term n)`.

**Used in.** The width parameter `w` throughout the switching-lemma and LMN
layer-reduction statements — the bound `CNF.width` is what
`NAndCircuit.toCNF_width_bounded` controls, and what the LMN circuit-compression
files (`CircuitCompression.lean`, `Depth3Switching.lean`,
`CircuitLayerReduction.lean`) track when replacing a circuit layer.
