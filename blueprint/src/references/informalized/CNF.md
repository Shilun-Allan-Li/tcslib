<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: CNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# CNF formulas

**Definition.** `CNF n` is the `abbrev`
```
CNF (n : ℕ) := List (Term n)
```
a CNF formula is a list of clauses, each clause being a `Term n =
List (Literal n)` but read *disjunctively*. The conjunctive reading sits at the
top level.

Its semantics and measure are:

- `CNF.evalClause t x = t.any (fun l => l.eval x)` — one clause holds when some
  literal does, so the empty clause is `false`;
- `CNF.eval c x = c.all (fun t => CNF.evalClause t x)` — all clauses must hold,
  so the empty CNF is identically `true`;
- `CNF.width c = (c.map Term.width).foldr max 0` — the maximum clause width.

**Remark.** `CNF n` is definitionally the same type as `DNF n`; the two
abbreviations differ only in intended reading, which is realised by `CNF.eval`
(`all`-of-`any`) versus `DNF.eval` (`any`-of-`all`). The reused `Term` name for
clauses is why clause width is measured by `Term.width`.

**Used in.** The width-`w` CNF is the dual input to the switching-lemma
machinery; `NAndCircuit.toCNF` produces one from a normal-form AND-circuit, with
`NAndCircuit.node_eval_eq_toCNF_eval`, `toCNF_terms_nodup`, and
`toCNF_width_bounded` as its correctness package.
