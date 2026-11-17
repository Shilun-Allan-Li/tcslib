<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignQueryCheck.negateQueries_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Negated Queries

**Claim.** If a set of sign predicates is closed under independently negating inputs and a sign query check’s predicate belongs to that set, then the predicate of the check obtained by negating the chosen queries also belongs to the set.

**Proof.** By definition, negating the queries of the check replaces its predicate by the original predicate with precisely the selected inputs negated. The assumed closure property applies to the original predicate in the set and to this choice of input positions, so the resulting predicate is also in the set.
