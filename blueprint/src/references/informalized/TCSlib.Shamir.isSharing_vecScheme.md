<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Vector.lean :: TCSlib.Shamir.isSharing_vecScheme -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise Vector Sharing

**Claim.** For each fixed coordinate $x$, the shares produced by the vector Shamir scheme form a sharing of $v(x)$ with degree bound less than $k$.

**Proof.** Fix the coordinate $x$. The vector scheme's share at party $i$, evaluated at coordinate $x$, is exactly the scalar Shamir share of the secret $v(x)$ with randomness polynomial $q(x)$. The scalar sharing theorem states that these shares form a sharing of $v(x)$ with the required degree bound (`isSharing_share`). Applying it to this secret and randomness proves the claim.

**Key facts.** `TCSlib.Shamir.isSharing_share`.
