<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinComplexity.lean :: CommunicationComplexity.PrivateCoin.le_communicationComplexity_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower-bound characterization

**Claim.** The natural number $n$ is at most the private-coin complexity exactly when every coin-tape protocol that meets the error bound has communication cost at least $n$.

**Proof.** Unfold the complexity as the iterated infimum over Alice's tape length, Bob's tape length, protocols, and proofs that the error bound is met. An element is at most an infimum exactly when it is at most every indexed value. Here each index includes an error-validity proof, and the corresponding value is the protocol's cost. Thus the inequality is equivalent to requiring cost at least $n$ for every choice of tape lengths and every protocol satisfying the error guarantee.
