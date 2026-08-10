<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating an AND-rooted normal-form circuit

**Definition.** `NAndCircuit n` and `NOrCircuit n` are a `mutual` pair of
inductives describing *alternating* circuits: each has a `clause` constructor
holding a literal list together with a proof `(lits.map Lit.idx).Nodup` (no
variable repeats inside a clause), and a `node` constructor whose children are
circuits of the *other* type. `NAndCircuit` is the AND-rooted one.

`NAndCircuit.eval` is defined in a `mutual` block with `NOrCircuit.eval`, by
recursion on the constructor:

- `.clause lits _, x => lits.foldr (fun l acc => l.eval x && acc) true` — the
  conjunction of the clause's literals, empty clause giving `true`;
- `.node cs, x => cs.foldr (fun c acc => c.eval x && acc) true` — the
  conjunction of its `NOrCircuit` children, calling `NOrCircuit.eval`.

The `Nodup` proof carried by `clause` is ignored by evaluation; it is a
by-construction invariant, extracted when needed by
`NAndCircuit.clause_nodup` and used via `Lit.eq_of_idx_eq_of_mem_nodup`
(two literals of a clause sharing a variable index are equal).

**Used in.** The correctness lemmas for `Circuit.toNAnd` / `Circuit.toNOr`, which
compare `NAndCircuit.eval` with `Circuit.eval`, and for the forgetful map
`NAndCircuit.toCircuit`. `NOrCircuit.eval` is the dual, folding with `||` from
`false`.
