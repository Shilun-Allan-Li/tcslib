<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/OneWay.lean :: CommunicationComplexity.Deterministic.OneWay.communicationComplexity_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of one-way cost bounds

**Claim.** The one-way deterministic communication complexity of a function is at most $n$ exactly when there exists a one-way protocol computing that function with bit cost at most $n$.

**Proof.** The one-way communication complexity is the infimum, in the extended natural numbers, of the costs of all protocols computing the function. The infimum-to-bound characterization (`enat_iInf_le_coe_iff`) says that this infimum is at most the natural number $n$ exactly when some indexed value in the family is at most $n$. Here an index consists of a protocol together with a proof that it computes the function. Unpacking that index yields precisely a protocol computing the function whose cost is at most $n$.

**Key facts.** `CommunicationComplexity.Internal.enat_iInf_le_coe_iff`.
