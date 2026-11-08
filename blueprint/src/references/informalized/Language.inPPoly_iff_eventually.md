<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: Language.inPPoly_iff_eventually -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Eventual Polynomial Size Characterization

**Claim.** A Boolean language has polynomial-size circuit families with fan-in at most two exactly when some such family recognizes it and has size at most $n^c$ for all $n\ge 2$, for some natural number $c$.

**Proof.** Suppose the language has size at most $a(n+1)^k$ for every $n$. For $n\ge2$, we have $a\le n^a$ and $n+1\le n^2$, so $a(n+1)^k\le n^a(n^2)^k=n^{a+2k}$. The original circuit family therefore gives the required eventual bound with exponent $a+2k$. Conversely, suppose a family has size at most $n^c$ for $n\ge2$. Set $a$ equal to the sum of its sizes at lengths zero and one, plus one. Since $(n+1)^c\ge1$, the size at either exceptional length is at most $a(n+1)^c$. For $n\ge2$, the assumed bound and $n^c\le(n+1)^c$ give the same estimate. The family thus has a polynomial bound at every length, and its fan-in and recognized language are unchanged.
