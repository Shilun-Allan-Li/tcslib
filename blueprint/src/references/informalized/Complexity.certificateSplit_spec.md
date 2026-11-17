<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.certificateSplit_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of certificate split search

**Claim.** The bounded certificate split search at length $m$ returns $n$ if and only if $n+(C+1)(n+1)^c=m$.

**Proof.** If the search returns $n$, the list-search specification says that its predicate holds at $n$. The predicate is equality with $m$, giving the stated equation. Conversely, assume the equation. Its nonnegative summands imply $n\le m$, so $n$ is among the candidates from $0$ through $m$. The search thus cannot fail. If it returns some candidate $j$, that candidate satisfies the same equation. Strict increase of the padded-length function (`Complexity.certificateTotal_strictMono`) then forces $j=n$, so the search returns $n$.

**Key facts.** `Complexity.certificateTotal_strictMono`.
