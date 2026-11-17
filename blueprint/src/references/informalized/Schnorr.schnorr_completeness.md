<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SchnorrProtocol.lean :: Schnorr.schnorr_completeness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completeness of the Schnorr Protocol

**Claim.** For an element $g$ of order $q$, the honest Schnorr transcript with commitment $a=g^r$ and response $s=r+cw$ satisfies the verifier equation for public key $g^w$.

**Proof.** Substituting the definitions, the verifier equation becomes $g^{(r+cw).\mathrm{val}}=g^{r.\mathrm{val}}g^{w.\mathrm{val}c.\mathrm{val}}$. Combine the powers on the right to obtain exponent $r.\mathrm{val}+w.\mathrm{val}c.\mathrm{val}$. Because $g$ has order $q$, two natural-number exponents give the same power of $g$ whenever they are congruent modulo $q$. The canonical representative of a sum in $\mathbb{Z}_q$ is congruent modulo $q$ to the sum of the representatives, and the representative of a product is congruent to the product of the representatives. Applying these facts shows that the two exponents are congruent modulo $q$, proving the verifier equation.
