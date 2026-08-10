<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: CNF.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluation of a CNF formula

**Definition.** A CNF formula is a list of clauses
(`abbrev CNF (n : ℕ) := List (Term n)`), and for `c : CNF n`,
`x : Fin n → Bool`,

`CNF.eval c x = c.all (fun t => CNF.evalClause t x)`,

so `c` is true at `x` exactly when *every* clause is satisfied, each clause being
read disjunctively by `CNF.evalClause`.

Being a `List.all`, the empty CNF evaluates to `true`: the empty conjunction of
clauses is vacuously satisfied.

**Remark.** `CNF n` and `DNF n` are the *same* type (`List (Term n)`); only the
evaluators differ — `CNF.eval` is `all`-of-`any` while `DNF.eval` is
`any`-of-`all`. This is what makes the De Morgan duality step `cnfToDualDNF` in
`Switching.lean` a statement about two functions on one datatype.

**Used in.** The CNF side of the switching lemma
(`TCSlib/BooleanAnalysis/Switching.lean`, including the decision-tree agreement
inductions and `cnfToDualDNF`) and the LMN files
(`LMN/CircuitHelpers.lean`, `LMN/CircuitCompression.lean`).
