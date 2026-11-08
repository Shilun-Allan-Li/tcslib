<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.verifier_strip_bridge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of stripping procedures

**Claim.** The procedure that returns the prefix before the last $1$ in a binary string, undefined if there is no $1$, agrees with recursive stripping of a marked certificate.

**Proof.** Fix a string $v$ and split according to the result of the recursive procedure. If it is undefined, the characterization of that procedure says that $v$ consists entirely of zeros (\texttt{Complexity.stripCertificate_spec}). Such a string has no $1$, so the last-one procedure is undefined too. If the recursive procedure returns $u$, the same characterization gives $v=u\mathbin{++}[1]\mathbin{++}0^k$ for some $k\ge0$. The final $1$ in this string is the displayed one, so removing it and the trailing zeros leaves exactly $u$. Thus the two procedures agree in both cases.

**Key facts.** `Complexity.stripCertificate_spec`.
