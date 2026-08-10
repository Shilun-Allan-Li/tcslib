<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NAndCircuit.clauseToTerm_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The width of a converted AND-clause is its literal count

**Claim.** For `lits : List (Lit n)` with `h : (lits.map Lit.idx).Nodup`,
`Term.width (NAndCircuit.clause lits h).clauseToTerm = lits.length`. Since
`Term.width` is `List.length` and `clauseToTerm` on a clause is
`lits.map Lit.toLiteral`, this is just the statement that `List.map` preserves
length; the `Nodup` hypothesis is inherited from the `clause` constructor and
plays no role.

**Proof.** One line: `simp [NAndCircuit.clauseToTerm, Term.width]`, which unfolds
both definitions and applies `List.length_map`.

**Used in.** `NOrCircuit.toDNF_width_bounded`, where the per-clause bound
`lits.length ≤ w` is transported to a bound on the width of the resulting DNF
term (`NAndCircuit.clauseToTerm_width lits h ▸ hl`).
