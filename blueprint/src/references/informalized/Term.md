<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Term -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Terms as lists of literals

**Definition.** `Term n` is the `abbrev`
```
Term (n : ℕ) := List (Literal n)
```
a term is just a list of literals on `n` variables, read as their conjunction.
Being an `abbrev` (reducible), a `Term n` *is* a `List (Literal n)` to the
elaborator, so the whole `List` API — `length`, `map`, `all`, `any`, membership,
`Nodup` — applies to terms with no coercion.

Two definitions give it structure:

- `Term.width t = t.length` — the number of literals in the term;
- `Term.eval t x = t.all (fun l => l.eval x)` — conjunctive semantics, so the
  empty term evaluates to `true`.

**Remark.** Nothing forbids repeated or contradictory literals in a `Term n`; a
no-repeated-variable condition, where needed, is imposed separately (e.g. the
`Nodup` fields of the `NAndCircuit` / `NOrCircuit` clauses, or the
`toCNF_terms_nodup` / `toDNF_terms_nodup` lemmas).

**Used in.** Both formula types are lists of terms: `DNF n = List (Term n)`
(terms read disjunctively at the top) and `CNF n = List (Term n)` (the same
lists, with each term read as a clause via `CNF.evalClause`). `Term.width` is
the quantity measured by `DNF.width` and `CNF.width`.
