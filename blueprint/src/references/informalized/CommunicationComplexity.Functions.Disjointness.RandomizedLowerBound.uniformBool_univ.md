<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total mass of the uniform bit law

**Claim.** The real-valued mass of the whole Boolean space under the uniform bit law is $1$.

**Proof.** The mass of any set under the uniform bit law is the number of its elements divided by $2$ (`uniformBool_real`). The whole Boolean space has two elements, so its mass is $2/2=1$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_real`.
