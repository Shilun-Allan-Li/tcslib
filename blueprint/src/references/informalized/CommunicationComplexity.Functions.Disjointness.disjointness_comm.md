<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncDisjointness.lean :: CommunicationComplexity.Functions.Disjointness.disjointness_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Disjointness

**Claim.** The set disjointness function is unchanged when its two set arguments are exchanged.

**Proof.** By definition, the function decides whether the two sets are disjoint. Disjointness is symmetric in its arguments, so the propositions being decided are equivalent after swapping the sets; their Boolean decisions are therefore equal.
