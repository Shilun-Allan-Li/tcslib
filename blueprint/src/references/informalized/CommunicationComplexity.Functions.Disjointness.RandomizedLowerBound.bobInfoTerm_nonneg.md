<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.bobInfoTerm_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Bob information

**Claim.** For every positive $n$ and deterministic protocol $p$, Bob’s special-coordinate bit and the transcript have nonnegative conditional mutual information under the disjoint-conditioned hard-sample distribution, given Bob’s conditioning variable.

**Proof.** By definition, Bob’s information term is the conditional mutual information of Bob’s special bit and the transcript given Bob’s conditioning variable. Conditional mutual information is nonnegative (`ProbabilityTheory.condMutualInfo_nonneg`), which proves the claim.
