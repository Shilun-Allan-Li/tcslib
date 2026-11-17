<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.paddedVerifier_no_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# All-Zero Padding Is Rejected

**Claim.** Appending $(C+1)(|x|+1)^c$ zeros to any binary string $x$ produces a string outside the padded verifier for $C,c,V$.

**Proof.** Apply the exact-boundary characterization to the appended zero block, whose length is $(C+1)(|x|+1)^c$. Membership would require that stripping a certificate from this block yield some witness. But stripping an all-zero list always fails (`stripCertificate_false`). Thus the required witness cannot exist, and the padded verifier rejects the string.

**Key facts.** `Complexity.paddedVerifier_append`, `Complexity.stripCertificate_false`.
