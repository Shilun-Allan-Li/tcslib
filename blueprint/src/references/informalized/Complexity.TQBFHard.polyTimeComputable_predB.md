<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.polyTimeComputable_predB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Predicate Computation

**Claim.** The one-bit output of the predicate combining the initial, accepting, base, and level checks is polynomial-time computable.

**Proof.** The initial-configuration check, accepting-configuration check, base check, and disjunction of level checks are each polynomial-time computable by `pt_initB`, `pt_accB`, `pt_baseB`, and `pt_orB`. Polynomial-time computable one-bit predicates are closed under conjunction (`polyTimeComputable_and`), so combining the first two checks remains polynomial-time computable. Closure under disjunction (`polyTimeComputable_or`) combines the base check with the level-check disjunction. A final conjunction of these two results computes exactly the defining Boolean expression for the predicate bit.

**Key facts.** `Complexity.TQBFHard.pt_initB`, `Complexity.TQBFHard.pt_accB`, `Complexity.polyTimeComputable_and`, `Complexity.TQBFHard.pt_baseB`, `Complexity.TQBFHard.pt_orB`, `Complexity.polyTimeComputable_or`, `Complexity.polyTimeComputable_and`.
