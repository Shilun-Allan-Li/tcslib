<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# AND-rooted normal-form circuits

**Definition.** `BoolCircuit.NAndCircuit n` is an inductive type of Boolean
circuits on `n` variables whose root gate is an AND, declared `mutual`ly with
`NOrCircuit n` so that gate types strictly alternate down the tree. It has two
constructors:

- `clause (lits : List (Lit n)) (h : (lits.map Lit.idx).Nodup)` — a base
  conjunction of literals, carrying a proof that no variable index is repeated
  in the clause;
- `node (cs : List (NOrCircuit n))` — an AND gate over a list of OR-rooted
  subcircuits.

So alternation and clause-level deduplication are invariants *of the type*, not
side conditions on theorems: any inhabitant of `NAndCircuit n` is already in
normal form.

Its measures are defined by mutual recursion alongside the `NOrCircuit`
versions: `NAndCircuit.eval` (`foldr (&&)` over clause literals or children),
`NAndCircuit.litCount` (`lits.length`, or the sum over children),
`NAndCircuit.size` (`1` for a clause, `1 +` sum over children), and
`NAndCircuit.depth` (`0` for a clause, `1 +` max over children).

**Used in.** The normalization pass `Circuit.toNAnd` lands here, and
`toNAnd_eval`, `toNAnd_litCount`, `toNAnd_size_le` say the pass preserves
semantics and literal count and at most doubles size. `NAndCircuit.toCircuit`
is the forgetful map back to the unconstrained `Circuit n`; the `Nodup` field is
what `NAndCircuit.clause_nodup` and `Lit.eq_of_idx_eq_of_mem_nodup` consume.
