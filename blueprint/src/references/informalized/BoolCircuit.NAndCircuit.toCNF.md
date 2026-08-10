<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.toCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reading a depth-2 AND-of-ORs circuit as a CNF

**Definition.** `NAndCircuit.toCNF : NAndCircuit n → CNF n` turns a normal-form
AND-circuit into a `CNF n` (a `List (Term n)`, each term read as a disjunction) by
cases on the constructor:

- `.node cs ↦ cs.map NOrCircuit.clauseToTerm` — an AND-node over OR-children
  becomes the list of their literal lists, each `BoolCircuit.Lit` converted by
  `Lit.toLiteral` (which flips the `sign`/`neg` convention);
- `.clause _ _ ↦ []` — a bare clause is not depth-2, so it is sent to the empty
  CNF (which `CNF.eval` reads as `true`).

So the conversion is only meaningful on `.node` circuits whose children are all
`NOrCircuit.clause`s; that well-formedness assumption appears explicitly as a
hypothesis on the lemmas about it, not in the definition. The `.clause` branch is a
total-function default, not a mathematical claim.

**Used in.** `NAndCircuit.node_eval_eq_toCNF_eval` (same file), which proves
`(NAndCircuit.node cs).eval x = CNF.eval (NAndCircuit.node cs).toCNF x` under the
hypothesis that every `c ∈ cs` is an `NOrCircuit.clause`.
