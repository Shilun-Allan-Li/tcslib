<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Vector.lean :: TCSlib.Shamir.vecScheme_perfectPrivacy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect privacy for vector secrets

**Claim.** For every unauthorized finite set of parties and every pair of vector secrets, there is a bijection of the randomness space that makes the shares of the second secret under transformed randomness agree on that set with the shares of the first secret under the original randomness.

**Proof.** Fix an unauthorized set and the two vector secrets. For each coordinate, scalar perfect privacy supplies a bijection of the scalar randomness space and guarantees equality of the resulting shares at every party in the set. These coordinatewise bijections combine to a bijection of the function-valued randomness space: apply the chosen bijection separately in each coordinate. For any randomness function and any party in the set, the share equality holds at each coordinate by the scalar guarantee. Hence the two vector-valued shares are equal.

**Key facts.** `TCSlib.Shamir.perfectPrivacy`.
