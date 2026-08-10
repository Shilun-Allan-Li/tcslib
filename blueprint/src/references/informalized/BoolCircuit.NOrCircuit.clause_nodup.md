<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NOrCircuit.clause_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reading off the Nodup invariant of an OR-clause

**Claim.** If `c : NOrCircuit n` is of the form `NOrCircuit.clause lits h`,
then `(lits.map Lit.idx).Nodup` holds. As in the AND case, the `Nodup` proof
`h` is implicit and the equation `c = NOrCircuit.clause lits h` is an unnamed,
unused hypothesis.

**Proof.** Immediate: the body is `:= h`, the implicit hypothesis itself.

**Remark.** The `NOrCircuit`-side twin of `NAndCircuit.clause_nodup`; both are
accessors for the invariant that the `clause` constructor of the mutually
defined normal-form circuit types stores, rather than substantive lemmas.
