<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.paddedVerifier_witness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded and Bounded Witnesses

**Claim.** There is a suffix of length $(C+1)(|x|+1)^c$ that places $x$ in the padded verifier language exactly when there is a witness $u$ of length at most $C(|x|+1)^c$ whose pair encoding with $x$ belongs to $V$.

**Proof.** For the forward implication, apply the characterization of membership for a string formed by appending a suffix of the specified length (`Complexity.paddedVerifier_append`). It supplies a witness $u$ whose certificate is extracted from that suffix, together with the required length bound and membership of the pair encoding in $V$.

For the reverse implication, start with such a $u$. The certificate-room inequality (`Complexity.certificate_room`) gives $|u|+1\le (C+1)(|x|+1)^c$. Thus we can fill the remaining length with zeros: set $k=(C+1)(|x|+1)^c-(|u|+1)$ and take the suffix $v=u\,1\,0^k$. Its length is exactly $(C+1)(|x|+1)^c$. The padding property (`Complexity.stripCertificate_pad`) says that extracting a certificate from this suffix returns $u$. The same membership characterization then shows that appending $v$ to $x$ places the result in the padded verifier language, using the given length bound and pair-encoding membership.

**Key facts.** `Complexity.paddedVerifier_append`, `Complexity.certificate_room`, `Complexity.stripCertificate_pad`.
