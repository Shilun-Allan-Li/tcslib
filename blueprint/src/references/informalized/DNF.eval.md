<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: DNF.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluation of a DNF formula

**Definition.** A DNF formula is a list of terms
(`abbrev DNF (n : ℕ) := List (Term n)`), and for `d : DNF n`,
`x : Fin n → Bool`,

`DNF.eval d x = d.any (fun t => t.eval x)`,

so `d` is true at `x` exactly when *at least one* of its terms is true at `x`,
each term being evaluated conjunctively by `Term.eval`.

Being a `List.any`, the empty DNF evaluates to `false`: the empty disjunction is
unsatisfiable.

**Remark.** Together with `Term.eval` this fixes the standard OR-of-ANDs reading
of the same nested-list data that `CNF.eval` reads as an AND-of-ORs.

**Used in.** The DNF side of the switching lemma
(`TCSlib/BooleanAnalysis/Switching.lean`, e.g. the decision-tree
`DNF.eval`/`DecisionTree.eval` agreement arguments and `cnfToDualDNF`) and the
LMN compression files (`LMN/CircuitCompression.lean`,
`LMN/CircuitHelpers.lean`).
