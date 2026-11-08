<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Vector.lean :: TCSlib.Shamir.vecScheme_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness for vector secrets

**Claim.** When $k>0$, the vector-valued scheme correctly reconstructs every vector secret from any finite set of at least $k$ parties, for every coordinatewise choice of randomness.

**Proof.** Fix an authorized set of parties, a vector secret, and its coordinatewise randomness. To prove equality of the reconstructed and original vectors, fix an arbitrary coordinate. At that coordinate, the vector scheme's reconstruction and shares are those of the scalar scheme, with secret and randomness given by that coordinate of the vector data. The scalar correctness theorem therefore identifies the reconstructed coordinate with the original one. Since this holds at every coordinate, the vectors are equal.

**Key facts.** `TCSlib.Shamir.correct`.
