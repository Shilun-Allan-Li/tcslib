<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComplexity.lean :: CommunicationComplexity.Internal.enat_iInf_le_coe_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Infimum Bound Witness Criterion

**Claim.** For a family of extended natural numbers $(f_i)_{i\in\iota}$ and a natural number $n$, its infimum is at most $n$ exactly when some member of the family is at most $n$.

**Proof.** If some $f_i\le n$, the infimum is at most that member and therefore at most $n$. Conversely, suppose every $f_i$ is strictly greater than $n$. Since the values are extended naturals, each finite value must then be at least $n+1$, while the infinite value is also at least $n+1$. Thus $n+1$ is a lower bound for the whole family, so the infimum is at least $n+1$. This contradicts the assumption that it is at most $n$.
