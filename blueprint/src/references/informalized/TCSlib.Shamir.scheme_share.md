<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.scheme_share -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Share evaluation

**Claim.** In the specified sharing scheme, the share of a secret using randomness $q$ for party $a$ is the value at $a$ of the polynomial $s+Xq(X)$.

**Proof.** The scheme's sharing map is defined to return the sharing polynomial evaluated at the party's label. Unfolding that definition gives exactly the stated evaluation.
