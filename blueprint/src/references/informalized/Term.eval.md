<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Term.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluation of a term as a conjunction

**Definition.** For `t : Term n` (a list of literals) and an assignment
`x : Fin n → Bool`,

`Term.eval t x = t.all (fun l => l.eval x)`,

i.e. the term is true exactly when *every* literal in the list is satisfied by
`x`, where each literal is evaluated by `Literal.eval` (`x l.var` if `l.neg` is
false, `!x l.var` if it is true).

Being a `List.all`, the empty term evaluates to `true`: the empty conjunction is
vacuously satisfied.

**Remark.** `Term n` is an `abbrev` for `List (Literal n)`, so the conjunctive
reading lives entirely in this function — the very same type is read
disjunctively by `CNF.evalClause`.

**Used in.** `DNF.eval` (a DNF is true when some term is), and throughout the
switching-lemma and LMN normal-form files
(`TCSlib/BooleanAnalysis/Switching.lean`,
`LMN/NormalFormConversion.lean`, `LMN/CircuitHelpers.lean`).
