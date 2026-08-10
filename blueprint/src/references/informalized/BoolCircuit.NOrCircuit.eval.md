<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NOrCircuit.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating an OR-rooted normal-form circuit

**Definition.** `NOrCircuit n` is the OR-rooted half of the `mutual` pair of
alternating normal-form circuits: a `clause` holding a literal list plus a proof
`(lits.map Lit.idx).Nodup`, or a `node` whose children are `NAndCircuit n`s.

`NOrCircuit.eval : NOrCircuit n → (Fin n → Bool) → Bool` is defined mutually with
`NAndCircuit.eval`, and is its exact dual — `||` in place of `&&`, seed `false`
in place of `true`:

- `.clause lits _, x => lits.foldr (fun l acc => l.eval x || acc) false`, the
  disjunction of the clause's literals (empty clause giving `false`);
- `.node cs, x => cs.foldr (fun c acc => c.eval x || acc) false`, the disjunction
  of its `NAndCircuit` children via `NAndCircuit.eval`.

Evaluation does not inspect the `Nodup` field; that invariant is recovered
separately by `NOrCircuit.clause_nodup`.

**Used in.** The evaluation-preservation lemmas for `Circuit.toNOr` and for the
forgetful coercion `NOrCircuit.toCircuit`, alongside the derived constants
`NOrCircuit.ofVar i` (a one-literal clause) and `NOrCircuit.constFalse` (the
empty disjunction), whose values follow from the two equations above.
