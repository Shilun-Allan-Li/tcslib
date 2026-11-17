<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHalt.lean :: Language.not_computablePred_mem_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noncomputability of Unary Languages

**Claim.** If membership in a set $S$ of natural numbers is not computable, then membership in the unary language of all-true Boolean lists whose lengths lie in $S$ is not computable.

**Proof.** Suppose, to the contrary, that there is a computable predicate deciding membership in the unary language. Apply it to the list of $n$ true bits. The map sending $n$ to this replicate list is computable, so composing it with the supposed decision procedure gives a computable predicate on natural numbers. The replicate-membership characterization says that this list belongs to the unary language exactly when $n\in S$ (Language.replicate_mem_unary_iff). Thus this composition decides membership in $S$, contradicting the hypothesis.

**Key facts.** `Language.replicate_mem_unary_iff`.
