<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_poly_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Payload Map

**Claim.** If $g$ is polynomial-time computable, then the function that decodes an input as a pair $(a,b)$ and returns the encoding of $(a,g(b))$ when decoding succeeds, and the empty word otherwise, is polynomial-time computable.

**Proof.** Take a machine for $g$ with bound $C(n+1)^c$. This bound is monotone in $n$: if $m\le n$, then $C(m+1)^c\le C(n+1)^c$. The pair payload mapping theorem (Turing.FinTM.computesFunInTime_pairMapSnd) therefore supplies a machine whose time on length $n$ is bounded by $K(n+1+C(n+1)^c)$ for some constant $K$. Since $n+1\le(n+1)^{c+1}$ and $(n+1)^c\le(n+1)^{c+1}$, this is at most $K(C+1)(n+1)^{c+1}$. Monotonicity of computation time allows the machine's bound to be enlarged to this polynomial bound (Turing.FinTM.ComputesInTime.mono).

**Key facts.** `Turing.FinTM.computesFunInTime_pairMapSnd`, `Turing.FinTM.ComputesInTime.mono`.
