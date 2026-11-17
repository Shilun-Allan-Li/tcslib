<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Conditioning.lean :: ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-space conditional mutual information

**Claim.** For finite probability spaces and finite-valued variables, identically distributed triples have equal conditional mutual information.

**Proof.** Because the value sets are finite, the variables have finite range. On the discrete measurable spaces in question, all six coordinate maps are measurable. Thus the general invariance theorem for conditional mutual information under equality of triple laws applies directly and yields the result.

**Key facts.** `ProbabilityTheory.IdentDistrib.condMutualInfo_eq`.
