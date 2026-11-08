<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.maxE3LinPredicates_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finiteness of E3 linear predicates

**Claim.** For each finite arity bound, the family of maximum E3 linear predicates is finite.

**Proof.** Each maximum E3 linear predicate is obtained by evaluating the predicate construction `e3LinPredicate` at a parameter. Thus the family is contained in the range of that construction, and the range of a function with finite domain is finite.
