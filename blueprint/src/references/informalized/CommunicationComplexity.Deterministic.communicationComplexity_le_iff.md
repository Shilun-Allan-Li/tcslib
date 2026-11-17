<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComplexity.lean :: CommunicationComplexity.Deterministic.communicationComplexity_le_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Protocol Threshold Characterization

**Claim.** For any function $f$ and natural number $n$, one has $D(f)\le n$ exactly when there is a deterministic protocol computing $f$ whose communication complexity is at most $n$.

**Proof.** By definition, $D(f)$ is the infimum, in the extended natural numbers, of the costs of protocols computing $f$. The infimum is at most the finite threshold $n$ exactly when at least one member of the indexed family is at most $n$ (\texttt{Internal.enat\_iInf\_le\_coe\_iff}). Here the family is indexed by a protocol together with a proof that it computes $f$. Thus the witness consists precisely of a protocol computing $f$ with cost at most $n.

**Key facts.** `CommunicationComplexity.Internal.enat_iInf_le_coe_iff`.
