<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.sigma_map_bool_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of a Boolean-indexed sum map

**Claim.** If each map $g_b$ is injective, then the map sending $(b,t)$ to $(b,g_b(t))$ on Boolean-indexed dependent pairs is injective.

**Proof.** Suppose two image pairs are equal. Their first coordinates must agree. If both indices are false, equality of the second coordinates and injectivity of $g_{m false}$ give equality of the original second coordinates. The same argument with $g_{m true}$ applies when both indices are true. If the indices differ, equality of the first coordinates is impossible. Thus the original pairs are equal.
