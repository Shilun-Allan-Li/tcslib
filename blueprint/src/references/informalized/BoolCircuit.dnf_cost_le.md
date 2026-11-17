<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.dnf_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Tree Construction Cost

**Claim.** If $s\le 2^n$, then $s\,\mathrm{treeCost}(n)+\mathrm{treeCost}(s)\le n2^n+1$.

**Proof.** First consider $n=0$. The hypothesis gives $s\le1$, so $s$ is either $0$ or $1$. In either case, evaluating the definition of tree cost gives the claimed inequality. Now suppose $n>0$, and write $n=m+1$. If $s=0$, the inequality follows directly from the definition. For $s>0$, the cost definition gives $\mathrm{treeCost}(m+1)=m$ and $\mathrm{treeCost}(s)=s-1$. From $s\le2^{m+1}$, multiplication by $m$ yields $sm\le 2^{m+1}m$. Since $(m+1)2^{m+1}=2^{m+1}m+2^{m+1}$, the left side of the desired bound is at most $2^{m+1}m+(s-1)$, which is at most $2^{m+1}m+2^{m+1}+1=(m+1)2^{m+1}+1$. This is the required bound.
