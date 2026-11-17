<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.complementLinear_natDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a complemented linear polynomial

**Claim.** For every natural number $n$, the polynomial $n-X$ has natural degree $1$.

**Proof.** Rewrite $n-X$ as $-(X-n)$. Negating a polynomial does not change its natural degree, and the linear polynomial $X-n$ has natural degree $1$. Therefore $n-X$ has natural degree $1$.
