<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.pairedVerifier_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of an encoded pair

**Claim.** The encoding of $(x,u)$ belongs to the paired verifier language exactly when $|u|=C(|x|+1)^c$ and the concatenation $xu$ belongs to $V$.

**Proof.** By definition, membership means there are strings whose decoding is the input and which satisfy the required payload-length and concatenation conditions. The decoder recovers exactly $(x,u)$ from the encoding (`pairDecode_pairEncode`), so the existential witnesses must be those two strings. Substituting them into the definition leaves precisely the stated length equality and language membership condition, proving both directions.

**Key facts.** `Turing.pairDecode_pairEncode`.
