<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.paddedVerifier_too_long -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection of Overlong Witnesses

**Claim.** If $|u1 0^k|=(C+1)(|x|+1)^c$ and $C(|x|+1)^c<|u|$, then $xu1 0^k$ is outside the padded verifier for $C,c,V$.

**Proof.** The suffix $v=u1 0^k$ has the exact length required by the boundary characterization, so membership would produce a string $u'$ obtained by stripping a certificate from $v$, with $|u'|\le C(|x|+1)^c$. Stripping this marked suffix recovers exactly $u$ (`stripCertificate_pad`), hence $u'=u$. The resulting length bound contradicts the assumed strict inequality $C(|x|+1)^c<|u|$. Therefore the padded verifier rejects.

**Key facts.** `Complexity.paddedVerifier_append`, `Complexity.stripCertificate_pad`.
