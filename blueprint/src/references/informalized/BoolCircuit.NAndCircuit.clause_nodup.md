<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit.clause_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reading off the Nodup invariant of an AND-clause

**Claim.** If `c : NAndCircuit n` is of the form `NAndCircuit.clause lits h`,
then `(lits.map Lit.idx).Nodup` holds. The `Nodup` proof `h` is an implicit
argument of the statement, and the equation `c = NAndCircuit.clause lits h`
is an unnamed hypothesis that is not used.

**Proof.** Immediate: the conclusion is literally the implicit hypothesis
`h`, so the body is `:= h`.

**Remark.** This is a deliberately granular accessor, not a theorem: it exists
so that a proof holding a clause equation can name the distinct-index
invariant that `NAndCircuit.clause` carries by construction, without
destructuring the constructor by hand. `NOrCircuit.clause_nodup` is the
mirror statement for OR-clauses.
