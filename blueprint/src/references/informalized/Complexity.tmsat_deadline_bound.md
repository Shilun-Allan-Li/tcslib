<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_deadline_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arithmetic deadline bound

**Claim.** For all natural numbers $K,B,e,C,c,n$, the stated deadline expression is bounded by the displayed polynomial in $n+1$.

**Proof.** Set $m=n+1$ and $d=\max(1,c)$. Since $d\geq 1$ and $d\geq c$, monotonicity of natural powers gives $m\leq m^d$ and $m^c\leq m^d$. Consequently, the quantity inside the power $e$ is at most $(C+3)m^d$: the terms $2n+2=2m$ and $1$ are bounded using $m\leq m^d$, and the term $C m^c$ is bounded using $m^c\leq m^d$. Raising to the power $e$ therefore bounds it by $(C+3)^e m^{ed}$. This latter quantity is at least $1$. It follows that $B$ times the powered expression, plus $1$, is at most $(B+1)(C+3)^e m^{ed}$. Finally, $K\leq K+1$; multiplying this inequality by the square of the preceding bound yields the claimed result, since squaring gives the factors $(B+1)^2$, $(C+3)^{2e}$, and $m^{2ed}$.
