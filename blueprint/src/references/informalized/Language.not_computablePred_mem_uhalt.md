<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHalt.lean :: Language.not_computablePred_mem_uhalt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noncomputability of the Unary Halting Language

**Claim.** The language of all-true Boolean lists whose lengths lie in the halting set has no computable membership predicate.

**Proof.** The halting set has no computable membership predicate (Nat.Partrec.Code.not_computablePred_mem_haltingSet). The noncomputability theorem for unary languages says that whenever a set of natural numbers has noncomputable membership, the language of all-true lists whose lengths lie in that set also has noncomputable membership (Language.not_computablePred_mem_unary). Applying it to the halting set gives the claim.

**Key facts.** `Nat.Partrec.Code.not_computablePred_mem_haltingSet`, `Language.not_computablePred_mem_unary`.
