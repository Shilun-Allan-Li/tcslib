<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.stripCertificate_pad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stripping a padded string

**Claim.** For every binary string $u$ and $k\in\mathbb{N}$, stripping $u$ followed by a $1$ and then $k$ zeros returns $u$.

**Proof.** Induct on $u$. If $u$ is empty, the string is a $1$ followed by $k$ zeros; the definition of stripping and the fact that a string of zeros strips to `none` give the result. If $u=b::u'$, the induction hypothesis says that stripping $u'$ followed by the marker and zeros returns $u'$. The recursive definition therefore prepends $b$ to that result, yielding $b::u'=u$.

**Key facts.** `Complexity.stripCertificate_false`.
