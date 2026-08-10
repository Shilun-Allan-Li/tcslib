<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.toDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reading a depth-2 OR-of-ANDs circuit as a DNF

**Definition.** `NOrCircuit.toDNF : NOrCircuit n → DNF n` turns a normal-form
OR-circuit into a `DNF n` (a `List (Term n)`, each term read as a conjunction) by
cases on the constructor:

- `.node cs ↦ cs.map NAndCircuit.clauseToTerm` — an OR-node over AND-children
  becomes the list of their literal lists, each `BoolCircuit.Lit` converted by
  `Lit.toLiteral` (which flips the `sign`/`neg` convention);
- `.clause _ _ ↦ []` — a bare clause is not depth-2, so it is sent to the empty
  DNF (which `DNF.eval` reads as `false`).

The conversion is therefore only meaningful on `.node` circuits whose children are
all `NAndCircuit.clause`s; that well-formedness assumption lives in the hypotheses
of the lemmas about it rather than in the definition, and the `.clause` branch is
just a totality default.

**Used in.** `NOrCircuit.node_eval_eq_toDNF_eval` (same file), which proves
`(NOrCircuit.node cs).eval x = DNF.eval (NOrCircuit.node cs).toDNF x` under the
hypothesis that every `c ∈ cs` is an `NAndCircuit.clause`.
