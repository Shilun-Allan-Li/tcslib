<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_certificate_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# TMSAT certificate characterization

**Claim.** A bit string $y$ belongs to $\mathrm{TMSAT}_c$ exactly when there is a bit string $w$ of length $|y|+1$ such that $yw$ belongs to the verifier language $V_c$.

**Proof.** Suppose first that $y$ is in $\mathrm{TMSAT}_c$, witnessed by strings $\alpha,x,u$ and numbers $n,t$. The length bounds for the encoded quadruple (`Complexity.tmsat_quad_bounds`) give $n\le |y|$. Extend $u$ by enough zeros to obtain a word $w$ of length $|y|+1$. Since $|u|=n$, taking the first $n$ bits of $w$ recovers $u$. Thus $y$ followed by $w$ satisfies the verifier’s format and its computation condition is the original witness condition.

Conversely, suppose such a certificate $w$ exists and $yw$ is in the verifier language. Its verifier witnesses include a decomposition $yw=y'w'$ with $w'$ of length $|y'|+1$ and $y'=y$. The equality of concatenated words, together with these length conditions, identifies the two pieces as $y'=y$ and $w'=w$. The same encoded-quadruple length bounds give $n\le |y|$, hence $n\le |w|$. Therefore the prefix of $w$ of length $n$ has length exactly $n$. Use that prefix as the padded string in the definition of $\mathrm{TMSAT}_c$; the verifier’s computation condition supplies the required accepting run.

**Key facts.** `Complexity.tmsat_quad_bounds`.
