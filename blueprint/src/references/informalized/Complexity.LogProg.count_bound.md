<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean :: Complexity.LogProg.count_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combinatorial Count Bound

**Claim.** For all natural parameters $q,n,K,W,cs,m,P$, the displayed product counting the bounded simulation configurations is at most the stated power of two times $(P+1)^2$.

**Proof.** Put $L=\logSpace(n)$ and $y=2n+2+m(2W+2)$. First bound the logarithmic length of the virtual input: elementary product estimates give $y\le 4(n+1)(W+1)(m+1)$. The standard inequalities $n+1\le 2^L$, $W+1\le 2^W$, and $m+1\le 2^m$ then imply $\logSpace(y)\le L+W+m+3$.

Set $E=(cs+1)(m+3)$ and $u=W+L+1$. The preceding logarithm estimate implies $W+1+(cs\logSpace(y)+1)\le Eu$. If $X=2(W+1+(cs\logSpace(y)+1))+1$, this gives $X\le(2E+1)u$. Bound the factors of the left-hand side separately: $q+1\le2^{q+1}$, $n+2\le2^{L+1}$, $3^{KX}\le2^{2KX}$, and $X^K\le2^{XK}$. Also $(2P+1)(2P+2)\le 2^2(P+1)^2$. Multiplying these inequalities collects the powers of two into an exponent at most $(q+4+3K(2E+1))u$. Substituting the definitions of $E$ and $u$ yields exactly the claimed right-hand side.
