<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.complementLinear_leadingCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading coefficient of a complemented linear polynomial

**Claim.** For every natural number $n$, the polynomial $n-X$ has leading coefficient $-1$.

**Proof.** Rewrite $n-X$ as $-(X-n)$, using the polynomial ring identities. The leading coefficient of a negated polynomial is the negative of its leading coefficient, and $X-n$ has leading coefficient $1$. Thus the leading coefficient is $-1$.
