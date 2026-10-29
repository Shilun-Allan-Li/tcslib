<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: dnfToDualCNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# De Morgan dualisation negates the value

**Claim.** For every `φ : DNF n` and every input `x : Fin n → Bool`,
`CNF.eval (dnfToDualCNF φ) x = !(DNF.eval φ x)`. That is, flipping the polarity of
every literal and reading the formula as a CNF computes the negation of the DNF.

**Proof.** Two nested list inductions, mirroring the two De Morgan laws.
After `simp only [dnfToDualCNF, CNF.eval, DNF.eval]` the goal is
`(φ.map _).all _ = !(φ.any _)`.

1. Outer induction on `φ` (`induction φ with | nil | cons hd tl ih`). The `nil` case is
   `true = !false`, closed by `simp`.
2. In the `cons` case, `List.all_cons` / `List.any_cons` split off the head; `ih`
   handles the tail and `Bool.not_or` turns `!(a || b)` into `!a && !b`. `congr 1`
   leaves only the head clause.
3. The head goal is `CNF.evalClause (hd.map Literal.flipNeg) x = !(Term.eval hd x)`,
   proved by an inner induction on the term `hd`, using `Literal.flipNeg_eval`
   (`l.flipNeg.eval x = !(l.eval x)`) and `Bool.not_and`.

**Used in.** `and_of_lit_children_cnf`, to certify that the CNF obtained by dualising
a gate's DNF computes the negated literal at that gate.
