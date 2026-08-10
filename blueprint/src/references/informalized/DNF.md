<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: DNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# DNF formulas

**Definition.** `DNF n` is the `abbrev`
```
DNF (n : ℕ) := List (Term n)
```
a DNF formula is a list of terms, read as their disjunction; since
`Term n = List (Literal n)`, a `DNF n` unfolds to a list of lists of literals.

Its semantics and measure are:

- `DNF.eval d x = d.any (fun t => t.eval x)` — at least one term must hold, so
  the empty DNF is identically `false`;
- `DNF.width d = (d.map Term.width).foldr max 0` — the maximum term width, and
  `0` for the empty formula.

**Remark.** `DNF n` and `CNF n` are *the same type* (`List (Term n)`), both
reducible abbreviations; only the evaluation functions differ — `DNF.eval` is
`any`-of-`all`, whereas `CNF.eval` is `all`-of-`any` (through
`CNF.evalClause`). So a term list can be handed to either interpreter and Lean
will not object; the intended reading is carried entirely by which `eval` is
applied.

**Used in.** The width-`w` DNF is the object the switching lemma converts to a
shallow decision tree; on the circuit side `NOrCircuit.toDNF` produces one, with
`NOrCircuit.node_eval_eq_toDNF_eval` and `toDNF_width_bounded` relating it to
the circuit it came from.
