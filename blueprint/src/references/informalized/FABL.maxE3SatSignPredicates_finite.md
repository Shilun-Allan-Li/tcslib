<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.maxE3SatSignPredicates_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finiteness of signed E3-SAT predicates

**Claim.** For each finite arity bound, the family of maximum E3-SAT sign predicates is finite.

**Proof.** Every maximum E3-SAT sign predicate is produced by the construction `e3SatSignClause` from one of its parameters. Hence the family is contained in the range of that construction, which is finite because its parameter type is finite.
