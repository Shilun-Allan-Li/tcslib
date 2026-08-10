<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: NOrCircuit.clauseToTerm_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Converting an OR-clause preserves `Nodup`

**Claim.** For `lits : List (Lit n)` with `h : (lits.map Lit.idx).Nodup`, the CNF
clause `(NOrCircuit.clause lits h).clauseToTerm` is duplicate-free. This is the
OR-side mirror of `NAndCircuit.clauseToTerm_nodup`: the two `clauseToTerm`
definitions have literally the same body, `lits.map Lit.toLiteral`, and differ
only in which of the two mutually-defined circuit types they destructure.

**Proof.** One line: `convert NAndCircuit.clauseToTerm_nodup lits h using 1`.
Because the two conversions unfold to the same list, a single congruence step
identifies the goal with the already-proved AND-clause statement.

**Used in.** `NAndCircuit.toCNF_terms_nodup`, which lifts it to every clause of a
converted CNF.
