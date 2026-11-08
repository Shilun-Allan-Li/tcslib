<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.certificateSplit_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Completeness of certificate split search

**Claim.** The stated claim says that if $n+C(n+1)^c=m$, then the certificate split search at length $m$ returns $n$.

**Proof.** The supplied proof source is inconsistent with the supplied declarations, so it does not establish this claim as written. The search tests the equation $k+(C+1)(k+1)^c=m$. Its specification therefore yields that equation for a returned value $k$. But the proof then composes it with the hypothesis $n+C(n+1)^c=m$ and applies injectivity of the function $r\mapsto r+C(r+1)^c$. These equations have different coefficients, so the composition and injectivity step do not follow. The theorem would need a matching search predicate, hypothesis, and strict-monotonicity fact before this argument could prove completeness.

**Key facts.** `Complexity.certificateSplit_none_iff`, `Complexity.certificateSplit_spec`, `Turing.certificateLength_strictMono`.

**Caveat.** The provided proof route has a coefficient mismatch: the search and its specification use $C+1$, while the hypothesis and strict-monotonicity lemma use $C$. The proof cannot be validated as supplied.
