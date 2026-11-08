<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.certificateSplit_none_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Failure of certificate split search

**Claim.** The bounded search returns no result exactly when there is no natural number $n$ satisfying $n+C(n+1)^c=m$.

**Proof.** By the characterization of a failed list search (`List.find?_eq_none`), failure means that every candidate in the search range fails its tested equation. If some $n$ satisfies $n+C(n+1)^c=m$, then $n\le m$ since all terms are nonnegative, so $n$ lies in the range; it is therefore a successful candidate, contradicting failure. Conversely, if the search has a successful candidate, that candidate satisfies the tested equation. Rewriting the test's coefficient gives the corresponding certificate-length equation, contradicting the assumed absence of such an $n$.

**Caveat.** The supplied search predicate tests $n+(C+1)(n+1)^c=m$, but the lemma's claimed right-hand side uses $C$. As written, the converse does not follow; the proof source appears to rely on an unstated or mismatched equation.
